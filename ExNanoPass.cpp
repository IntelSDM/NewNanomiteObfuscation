#include "ExNanoPass.h"
#include "NanomiteCommon.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <cstring>
#include <random>
#include <vector>

using namespace llvm;

cl::opt<bool> ExNanoEnable("obfexnano", cl::init(true), cl::desc("Enables Exception Nanomites"));

static constexpr unsigned MinSites = 1;
static constexpr bool SkipLoops = true;
static constexpr unsigned MaxSitesPerFn = 32;
static constexpr bool Harvest = true;
static constexpr unsigned HarvestDepth = 8;
static constexpr unsigned UD2Pct = 20;
static constexpr unsigned DecoyPct = 15;
static constexpr unsigned AVPct = 10;
static constexpr unsigned AVDepth = 8;

static constexpr uint64_t HashGoldenA = 0x9E3779B97F4A7C15ULL;
static constexpr uint64_t HashMixA = 0xC6BC279692B5C323ULL;
static constexpr uint64_t HashGoldenB = 0xC2B2AE3D27D4EB4FULL;
static constexpr uint64_t HashMixB = 0x165667B19E3779F9ULL;
static constexpr uint64_t HashGoldenC = 0x85EBCA77C2B2AE63ULL;
static constexpr uint64_t HashMixC = 0xA24BAED4963EE407ULL;

struct ExNanoSite
{
    Function* f;
    BasicBlock* faultbb;
    BasicBlock* targetbb;
    uint64_t siteid;
    uint64_t poll1;
    uint64_t poll2;
    bool p1fromharvest = false;
    bool p2fromharvest = false;
    bool isud2 = false;
    bool isav = false;
    bool hasdecoy = false;
    Function* decoyf = nullptr;
};

static std::vector<ExNanoSite> SiteList;
// decoy pool stores Function* directly rather than BlockAddress of entry the LLVM verifier rejects blockaddress of an entry block, and a Function* resolves at image load to the function's first byte VA just as the entry blockaddress would
static std::vector<Function*> DecoyPool;
static uint64_t BuildKey = 0;
static std::mt19937 RNG(std::random_device{}());

static uint64_t NextNonce()
{
    std::uniform_int_distribution<uint64_t> dist(1, ~0ULL);
    return dist(RNG);
}

static void InitBuildKey()
{
    std::uniform_int_distribution<uint64_t> dist(1, ~0ULL);
    BuildKey = dist(RNG);
}

static bool RollPercent(unsigned pct)
{
    if (pct == 0) return false;
    if (pct >= 100) return true;
    std::uniform_int_distribution<unsigned> dist(0, 99);
    return dist(RNG) < pct;
}

static uint64_t HashRegsImpl(uint64_t a, uint64_t b, uint64_t golden, uint64_t mix)
{
    uint64_t x = a + golden;
    x ^= b;
    x = (x << 23) | (x >> 41);
    x *= mix;
    x ^= x >> 32;
    return x;
}

static uint64_t HashRegsA(uint64_t a, uint64_t b)
{
    return HashRegsImpl(a, b, HashGoldenA, HashMixA);
}

static uint64_t HashRegsB(uint64_t a, uint64_t b)
{
    return HashRegsImpl(a, b, HashGoldenB, HashMixB);
}

static uint64_t HashRegsC(uint64_t a, uint64_t b)
{
    return HashRegsImpl(a, b, HashGoldenC, HashMixC);
}

static void BuildDecoyPool(Module& m)
{
    DecoyPool.clear();
    for (Function& f : m)
    {
        if (f.isDeclaration()) continue;
        if (f.empty()) continue;
        if (f.getName().starts_with("__exnano_")) continue;
        DecoyPool.push_back(&f);
    }
}

static Function* PickDecoy(Function& current)
{
    if (DecoyPool.empty()) return nullptr;
    SmallVector<unsigned, 32> eligible;
    for (size_t i = 0; i < DecoyPool.size(); ++i)
        if (DecoyPool[i] != &current)
            eligible.push_back((unsigned)i);
    if (eligible.empty()) return nullptr;
    std::uniform_int_distribution<unsigned> dist(0, (unsigned)eligible.size() - 1);
    return DecoyPool[eligible[dist(RNG)]];
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga) return false;
    ConstantArray* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        ConstantStruct* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annstr = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annstr || !annstr->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annstr->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasExNanoOptIn(Function& f)
{
    if (HasAnnotationTag(f, "exnano")) return true;
    if (HasAnnotationTag(f, "obfus") && IsAssignedToPass(f, "exnano")) return true;
    return false;
}

static bool HasExNanoOptOut(Function& f)
{
    return HasAnnotationTag(f, "noexnano") || HasAnnotationTag(f, "noobfus");
}

static bool BranchParentIsEHPad(BranchInst* br)
{
    BasicBlock* p = br->getParent();
    return p && p->isEHPad();
}

static bool BranchTargetIsEHPad(BranchInst* br)
{
    for (BasicBlock* succ : br->successors())
        if (succ && succ->isEHPad()) return true;
    return false;
}

static bool BranchTargetIsUnreachableOnly(BranchInst* br)
{
    if (br->getNumSuccessors() != 1) return false;
    BasicBlock* t = br->getSuccessor(0);
    if (!t || t->empty()) return false;
    return t->size() == 1 && isa<UnreachableInst>(t->getTerminator());
}

static bool BranchTargetHasPHI(BranchInst* br)
{
    if (br->getNumSuccessors() != 1) return false;
    BasicBlock* t = br->getSuccessor(0);
    if (!t || t->empty()) return false;
    return isa<PHINode>(&t->front());
}

static void CollectCandidates(Function& f, LoopInfo& li, std::vector<BranchInst*>& out)
{
    unsigned kept = 0;
    for (BasicBlock& bb : f)
    {
        auto* br = dyn_cast<BranchInst>(bb.getTerminator());
        if (!br) continue;
        if (br->isConditional()) continue;
        if (IsNanomiteClaimed(br)) continue;
        if (BranchParentIsEHPad(br)) continue;
        if (BranchTargetIsEHPad(br)) continue;
        if (BranchTargetIsUnreachableOnly(br)) continue;
        if (BranchTargetHasPHI(br)) continue;
        if (SkipLoops && li.getLoopFor(&bb)) continue;
        if (MaxSitesPerFn != 0 && kept >= MaxSitesPerFn) continue;
        ++kept;
        out.push_back(br);
    }
}

static SmallVector<uint64_t, 2> HarvestDominatingConsts(BranchInst* br, DominatorTree& dt, unsigned maxneeded)
{
    SmallVector<uint64_t, 2> out;
    DenseSet<uint64_t> seen;
    auto take = [&](Value* v)
    {
        if (out.size() >= maxneeded) return;
        auto* ci = dyn_cast<ConstantInt>(v);
        if (!ci) return;
        if (ci->getBitWidth() > 64) return;
        uint64_t x = ci->getZExtValue();
        if (x == 0 || x == 1 || x == ~0ULL) return;
        if (!seen.insert(x).second) return;
        out.push_back(x);
    };
    auto scan = [&](BasicBlock* bb)
    {
        for (Instruction& i : *bb)
        {
            for (Value* op : i.operands())
            {
                take(op);
                if (out.size() >= maxneeded) return;
            }
        }
    };
    scan(br->getParent());
    if (out.size() < maxneeded)
    {
        DomTreeNode* node = dt.getNode(br->getParent());
        unsigned depth = 0;
        while (out.size() < maxneeded && node && depth < HarvestDepth)
        {
            node = node->getIDom();
            if (!node) break;
            BasicBlock* bb = node->getBlock();
            if (!bb) break;
            scan(bb);
            ++depth;
        }
    }
    return out;
}

static Value* FindDominatingIntValue(BranchInst* br, DominatorTree& dt)
{
    auto take = [](Value* v) -> Value*
    {
        if (!v) return nullptr;
        if (isa<Constant>(v)) return nullptr;
        auto* i = dyn_cast<Instruction>(v);
        if (!i) return nullptr;
        Type* t = v->getType();
        if (!t->isIntegerTy()) return nullptr;
        unsigned bw = t->getIntegerBitWidth();
        if (bw < 32 || bw > 64) return nullptr;
        if (auto* ci = dyn_cast<CallInst>(i))
            if (ci->isInlineAsm()) return nullptr;
        return v;
    };
    for (Instruction& i : *br->getParent())
    {
        if (&i == br) break;
        if (Value* v = take(&i)) return v;
    }
    DomTreeNode* node = dt.getNode(br->getParent());
    unsigned depth = 0;
    while (node && depth < AVDepth)
    {
        node = node->getIDom();
        if (!node) break;
        BasicBlock* bb = node->getBlock();
        if (!bb) break;
        for (Instruction& i : *bb)
            if (Value* v = take(&i)) return v;
        ++depth;
    }
    return nullptr;
}

static InlineAsm* GetINT3Asm(LLVMContext& c)
{
    FunctionType* ty = FunctionType::get(Type::getVoidTy(c), {}, false);
    return InlineAsm::get(ty, "int3", "~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetUD2Asm(LLVMContext& c)
{
    FunctionType* ty = FunctionType::get(Type::getVoidTy(c), {}, false);
    return InlineAsm::get(ty, "ud2", "~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetPollAsm(LLVMContext& c)
{
    Type* voidt = Type::getVoidTy(c);
    Type* i64 = Type::getInt64Ty(c);
    FunctionType* ty = FunctionType::get(voidt, {i64, i64}, false);
    return InlineAsm::get(ty, "", "{r10},{r11},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetPollAsmAV(LLVMContext& c)
{
    Type* voidt = Type::getVoidTy(c);
    Type* i64 = Type::getInt64Ty(c);
    Type* ptrty = PointerType::get(c, 0);
    FunctionType* ty = FunctionType::get(voidt, {i64, i64, ptrty}, false);
    // 3-input pin asm pins r10/r11 AND rax with sideeffect=true so the backend doesn't shuffle %p out of rax between the pin in bb_A and the fault BB load
    return InlineAsm::get(ty, "", "{r10},{r11},{rax},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetAVLoadAsm(LLVMContext& c)
{
    FunctionType* ty = FunctionType::get(Type::getVoidTy(c), {}, false);
    // no input constraints means the backend emits NOTHING before this asm text at bb_fault's entry — first byte of bb_fault == first byte of this mov == fault RIP == BlockAddress(bb_fault)
    return InlineAsm::get(ty, "mov rax, qword ptr [rax]", "~{rax},~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static InlineAsm* GetJmpRegAsm(LLVMContext& c)
{
    Type* voidt = Type::getVoidTy(c);
    Type* ptrty = PointerType::get(c, 0);
    FunctionType* ty = FunctionType::get(voidt, {ptrty}, false);
    return InlineAsm::get(ty, "jmp $0", "r,~{dirflag},~{fpsr},~{flags}", true, false, InlineAsm::AD_Intel);
}

static void EmitSite(Function& f, BranchInst* br, DominatorTree& dt)
{
    LLVMContext& c = f.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* ptrty = PointerType::get(c, 0);
    BasicBlock* target = br->getSuccessor(0);
    Module* m = f.getParent();

    uint64_t poll1 = 0;
    uint64_t poll2 = 0;
    bool p1fromharvest = false;
    bool p2fromharvest = false;

    if (Harvest)
    {
        SmallVector<uint64_t, 2> harvested = HarvestDominatingConsts(br, dt, 2);
        if (harvested.size() >= 1) { poll1 = harvested[0]; p1fromharvest = true; }
        if (harvested.size() >= 2) { poll2 = harvested[1]; p2fromharvest = true; }
    }
    if (poll1 == 0) poll1 = NextNonce();
    if (poll2 == 0 || poll2 == poll1) poll2 = NextNonce();
    while (poll2 == poll1) poll2 = NextNonce();

    uint64_t siteid = NextNonce();

    bool useav = false;
    Value* domval = nullptr;
    if (RollPercent(AVPct))
    {
        domval = FindDominatingIntValue(br, dt);
        if (domval) useav = true;
    }

    bool useud2 = false;
    bool usedecoy = false;
    Function* decoy = nullptr;
    if (!useav)
    {
        useud2 = RollPercent(UD2Pct);
        usedecoy = RollPercent(DecoyPct);
        if (usedecoy)
        {
            decoy = PickDecoy(f);
            if (!decoy) usedecoy = false;
        }
    }

    const char* fbbname;
    if (useav) fbbname = "ExNanoFaultAV";
    else if (usedecoy && useud2) fbbname = "ExNanoFaultUD2Decoy";
    else if (usedecoy) fbbname = "ExNanoFaultInt3Decoy";
    else if (useud2) fbbname = "ExNanoFaultUD2";
    else fbbname = "ExNanoFaultInt3";

    BasicBlock* faultbb = BasicBlock::Create(c, fbbname, &f, target);
    {
        IRBuilder<> b(faultbb);
        if (useav)
        {
            b.CreateCall(GetAVLoadAsm(c));
        }
        else
        {
            b.CreateCall(useud2 ? GetUD2Asm(c) : GetINT3Asm(c));
            if (usedecoy)
            {
                auto* slot = new GlobalVariable(*m, ptrty, true, GlobalValue::PrivateLinkage, decoy, "ExNanoDecoySlot");
                slot->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
                Value* dec = b.CreateLoad(ptrty, slot, true, "DecoyVA");
                b.CreateCall(GetJmpRegAsm(c), {dec});
            }
        }
        // fault BB terminator must be indirectbr to target and NOT unreachable; LLVM silently rewrites BlockAddress of an unreachable BB to inttoptr(i64 1 to ptr), poisoning the table bake so enctarget becomes (1 + mask) and the dispatcher writes ctx->Rip=1
        Constant* targetba = BlockAddress::get(&f, target);
        IndirectBrInst* ibr = b.CreateIndirectBr(targetba, 1);
        ibr->addDestination(target);
    }

    {
        IRBuilder<> bp(br);
        if (useav)
        {
            Value* dv = domval;
            if (dv->getType()->getIntegerBitWidth() < 64)
                dv = bp.CreateZExt(dv, i64, "ExNanoDVZ");
            Constant* kernelor = ConstantInt::get(i64, 0xFFFF800000000000ULL);
            Value* orval = bp.CreateOr(dv, kernelor, "ExNanoOR");
            uint64_t persitemask = NextNonce() & 0x00007FFFFFFFFFFFULL;
            Constant* maskc = ConstantInt::get(i64, persitemask);
            Value* oob = bp.CreateXor(orval, maskc, "ExNanoOOB");
            Value* p = bp.CreateIntToPtr(oob, ptrty, "ExNanoP");
            bp.CreateCall(GetPollAsmAV(c), {
                ConstantInt::get(i64, poll1),
                ConstantInt::get(i64, poll2),
                p
            });
        }
        else
        {
            bp.CreateCall(GetPollAsm(c), {
                ConstantInt::get(i64, poll1),
                ConstantInt::get(i64, poll2)
            });
        }
    }

    br->setSuccessor(0, faultbb);
    ClaimNanomiteSite(br, "exnano");

    ExNanoSite s;
    s.f = &f;
    s.faultbb = faultbb;
    s.targetbb = target;
    s.siteid = siteid;
    s.poll1 = poll1;
    s.poll2 = poll2;
    s.p1fromharvest = p1fromharvest;
    s.p2fromharvest = p2fromharvest;
    s.isud2 = useud2;
    s.isav = useav;
    s.hasdecoy = usedecoy;
    s.decoyf = decoy;
    SiteList.push_back(s);
}

static StructType* GetEntryType(LLVMContext& c)
{
    return StructType::get(c, {PointerType::get(c, 0), Type::getInt64Ty(c), Type::getInt64Ty(c)}, false);
}

static GlobalVariable* EmitTable(Module& m, ArrayRef<ExNanoSite> sites)
{
    LLVMContext& c = m.getContext();
    StructType* entryt = GetEntryType(c);
    PointerType* ptrty = PointerType::get(c, 0);
    IntegerType* i64 = Type::getInt64Ty(c);

    SmallVector<Constant*, 4> entries;
    entries.reserve(sites.size() + 1);
    for (const ExNanoSite& s : sites)
    {
        Constant* faultba = BlockAddress::get(s.f, s.faultbb);
        Constant* targetba = BlockAddress::get(s.f, s.targetbb);
        Constant* targetint = ConstantExpr::getPtrToInt(targetba, i64);
        uint64_t h;
        if (s.isav) h = HashRegsC(s.poll1, s.poll2);
        else if (s.isud2) h = HashRegsB(s.poll1, s.poll2);
        else h = HashRegsA(s.poll1, s.poll2);
        uint64_t mask = h ^ BuildKey ^ s.siteid;
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enctarget = ConstantExpr::getAdd(targetint, maskc);
        Constant* siteidc = ConstantInt::get(i64, s.siteid);
        entries.push_back(ConstantStruct::get(entryt, {faultba, enctarget, siteidc}));
    }
    entries.push_back(ConstantStruct::get(entryt, {
        ConstantPointerNull::get(ptrty),
        ConstantInt::get(i64, 0),
        ConstantInt::get(i64, 0)
    }));

    ArrayType* arrt = ArrayType::get(entryt, entries.size());
    Constant* init = ConstantArray::get(arrt, entries);
    return new GlobalVariable(m, arrt, false, GlobalValue::InternalLinkage, init, "__exnano_table");
}

static Function* GetOrDeclareAddVEH(Module& m)
{
    const char* name = "AddVectoredExceptionHandler";
    if (Function* existing = m.getFunction(name)) return existing;
    LLVMContext& c = m.getContext();
    Type* ptrty = PointerType::get(c, 0);
    Type* i32 = Type::getInt32Ty(c);
    FunctionType* ty = FunctionType::get(ptrty, {i32, ptrty}, false);
    Function* f = Function::Create(ty, GlobalValue::ExternalLinkage, name, &m);
    f->setDLLStorageClass(GlobalValue::DLLImportStorageClass);
    return f;
}

static Value* EmitHashRegsIR(IRBuilder<>& b, Value* va, Value* vb, uint64_t golden, uint64_t mix, const Twine& tag)
{
    LLVMContext& c = b.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Value* x = b.CreateAdd(va, ConstantInt::get(i64, golden), tag + "Add");
    x = b.CreateXor(x, vb, tag + "Xor1");
    Value* xl = b.CreateShl(x, ConstantInt::get(i64, 23), tag + "Shl");
    Value* xh = b.CreateLShr(x, ConstantInt::get(i64, 41), tag + "LShr");
    x = b.CreateOr(xl, xh, tag + "Rol");
    x = b.CreateMul(x, ConstantInt::get(i64, mix), tag + "Mul");
    Value* xs = b.CreateLShr(x, ConstantInt::get(i64, 32), tag + "LShr2");
    x = b.CreateXor(x, xs, tag + "Xor2");
    return x;
}

static Function* EmitDispatch(Module& m, GlobalVariable* table, unsigned entriesplussentinel)
{
    LLVMContext& c = m.getContext();
    Type* i8 = Type::getInt8Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);
    StructType* entryt = GetEntryType(c);
    ArrayType* arrt = ArrayType::get(entryt, entriesplussentinel);

    FunctionType* ft = FunctionType::get(i32, {ptrty}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, "__exnano_dispatch", &m);
    f->addFnAttr(Attribute::NoUnwind);
    f->getArg(0)->setName("Ep");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* haveflt = BasicBlock::Create(c, "HaveFault", f);
    BasicBlock* loop = BasicBlock::Create(c, "Loop", f);
    BasicBlock* check = BasicBlock::Create(c, "Check", f);
    BasicBlock* cont = BasicBlock::Create(c, "Cont", f);
    BasicBlock* hit = BasicBlock::Create(c, "Hit", f);
    BasicBlock* miss = BasicBlock::Create(c, "Miss", f);

    Value* ep = f->getArg(0);

    Value* isbp = nullptr;
    Value* isud = nullptr;
    {
        IRBuilder<> b(entry);
        Value* erloc = b.CreateLoad(ptrty, ep, "ER");
        Value* code = b.CreateLoad(i32, erloc, "Code");
        Constant* bpcode = ConstantInt::get(i32, 0x80000003u);
        Constant* udcode = ConstantInt::get(i32, 0xC000001Du);
        Constant* avcode = ConstantInt::get(i32, 0xC0000005u);
        isbp = b.CreateICmpEQ(code, bpcode, "IsBP");
        isud = b.CreateICmpEQ(code, udcode, "IsUD");
        Value* isav = b.CreateICmpEQ(code, avcode, "IsAV");
        Value* isany = b.CreateOr(b.CreateOr(isbp, isud, "BPOrUD"), isav, "IsAny");
        b.CreateCondBr(isany, haveflt, miss);
    }

    Value* faultaddr = nullptr;
    {
        IRBuilder<> b(haveflt);
        Value* erloc = b.CreateLoad(ptrty, ep, "ER2");
        Value* addrslot = b.CreateGEP(i8, erloc, ConstantInt::get(i64, 16), "AddrSlot");
        faultaddr = b.CreateLoad(ptrty, addrslot, "FaultAddr");
        b.CreateBr(loop);
    }

    PHINode* iphi = nullptr;
    Value* entptr = nullptr;
    {
        IRBuilder<> b(loop);
        iphi = b.CreatePHI(i64, 2, "I");
        iphi->addIncoming(ConstantInt::get(i64, 0), haveflt);
        entptr = b.CreateGEP(arrt, table, {ConstantInt::get(i64, 0), iphi}, "EntPtr");
        Value* fp = b.CreateLoad(ptrty, entptr, "FaultBA");
        Value* isend = b.CreateICmpEQ(fp, ConstantPointerNull::get(ptrty), "IsEnd");
        b.CreateCondBr(isend, miss, check);
    }

    {
        IRBuilder<> b(check);
        Value* fp = b.CreateLoad(ptrty, entptr, "FaultBAC");
        Value* ishit = b.CreateICmpEQ(fp, faultaddr, "IsHit");
        b.CreateCondBr(ishit, hit, cont);
    }

    {
        IRBuilder<> b(cont);
        Value* inext = b.CreateAdd(iphi, ConstantInt::get(i64, 1), "INext");
        iphi->addIncoming(inext, cont);
        b.CreateBr(loop);
    }

    {
        IRBuilder<> b(hit);
        Value* tgtslot = b.CreateGEP(entryt, entptr, {ConstantInt::get(i32, 0), ConstantInt::get(i32, 1)}, "TgtSlot");
        Value* enctgt = b.CreateLoad(i64, tgtslot, "EncTgt");
        Value* sidslot = b.CreateGEP(entryt, entptr, {ConstantInt::get(i32, 0), ConstantInt::get(i32, 2)}, "SIDSlot");
        Value* sid = b.CreateLoad(i64, sidslot, "SID");
        Value* ctxslot = b.CreateGEP(i8, ep, ConstantInt::get(i64, 8), "CtxSlot");
        Value* ctx = b.CreateLoad(ptrty, ctxslot, "Ctx");
        Value* r10slot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xC8), "R10Slot");
        Value* r10 = b.CreateLoad(i64, r10slot, "R10");
        Value* r11slot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xD0), "R11Slot");
        Value* r11 = b.CreateLoad(i64, r11slot, "R11");
        Value* ha = EmitHashRegsIR(b, r10, r11, HashGoldenA, HashMixA, "HA");
        Value* hb = EmitHashRegsIR(b, r10, r11, HashGoldenB, HashMixB, "HB");
        Value* hc = EmitHashRegsIR(b, r10, r11, HashGoldenC, HashMixC, "HC");
        Value* hborc = b.CreateSelect(isud, hb, hc, "HBOrC");
        Value* h = b.CreateSelect(isbp, ha, hborc, "H");
        Constant* bkc = ConstantInt::get(i64, BuildKey);
        Value* hbk = b.CreateXor(h, bkc, "HXorBK");
        Value* mask = b.CreateXor(hbk, sid, "Mask");
        Value* tgt = b.CreateSub(enctgt, mask, "Tgt");
        Value* ripslot = b.CreateGEP(i8, ctx, ConstantInt::get(i64, 0xF8), "RipSlot");
        b.CreateStore(tgt, ripslot);
        b.CreateRet(ConstantInt::get(i32, (uint32_t)-1));
    }

    {
        IRBuilder<> b(miss);
        b.CreateRet(ConstantInt::get(i32, 0));
    }

    return f;
}

static Function* EmitInit(Module& m, Function* dispatch)
{
    const char* name = "__exnano_init";
    if (Function* existing = m.getFunction(name)) return existing;
    LLVMContext& c = m.getContext();
    Type* voidt = Type::getVoidTy(c);
    Type* i32 = Type::getInt32Ty(c);
    FunctionType* ft = FunctionType::get(voidt, {}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::NoUnwind);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    IRBuilder<> b(entry);
    Function* addveh = GetOrDeclareAddVEH(m);
    b.CreateCall(addveh, {ConstantInt::get(i32, 1), dispatch});
    b.CreateRetVoid();
    return f;
}

static bool EmitPlumbing(Module& m, ArrayRef<ExNanoSite> sites)
{
    if (m.getFunction("__exnano_dispatch")) return false;
    if (sites.empty()) return false;
    GlobalVariable* table = EmitTable(m, sites);
    Function* dispatch = EmitDispatch(m, table, (unsigned)sites.size() + 1);
    Function* init = EmitInit(m, dispatch);
    appendToGlobalCtors(m, init, 65535);
    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (f.getName().starts_with("__exnano_")) return false;
    if (HasExNanoOptOut(f)) return false;
    if (!HasExNanoOptIn(f)) return false;

    DominatorTree dt;
    dt.recalculate(f);
    LoopInfo li;
    li.analyze(dt);

    std::vector<BranchInst*> cands;
    CollectCandidates(f, li, cands);
    if (cands.empty()) return false;
    if (cands.size() < MinSites) return false;

    for (BranchInst* br : cands)
        EmitSite(f, br, dt);
    return true;
}

bool RunExNano(Module& m)
{
    if (!ExNanoEnable) return false;
    SiteList.clear();
    InitBuildKey();
    BuildDecoyPool(m);
    bool mutated = false;
    for (Function& f : m)
        mutated |= ProcessFunction(f);
    if (!SiteList.empty())
        mutated |= EmitPlumbing(m, SiteList);
    return mutated;
}

PreservedAnalyses ExNanoPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunExNano(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}