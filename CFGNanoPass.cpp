#include "CFGNanoPass.h"
#include "NanomiteCommon.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
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

#include <cstdio>
#include <cstring>
#include <random>
#include <vector>

using namespace llvm;

cl::opt<bool> CFGNanoEnable("obfcfgnano", cl::init(true), cl::desc("Enables CFG Nanomites"));

static constexpr unsigned MinSites = 1;
static constexpr bool SkipLoops = true;
static constexpr unsigned MaxSitesPerFn = 32;
static constexpr bool Harvest = true;
static constexpr unsigned HarvestDepth = 8;

static constexpr uint64_t HashGolden = 0xBF58476D1CE4E5B9ULL;
static constexpr uint64_t HashMix = 0x94D049BB133111EBULL;

struct CFGNanoSite
{
    Function* f;
    BasicBlock* landingbb;
    BasicBlock* targetbb;
    uint64_t siteid;
    uint32_t poll;
    bool pollfromharvest = false;
    unsigned vtslot = 0;
};

static std::vector<CFGNanoSite> SiteList;
static uint64_t BuildKey = 0;
static std::mt19937 RNG(std::random_device{}());

static uint64_t NextNonce()
{
    std::uniform_int_distribution<uint64_t> dist(1, ~0ULL);
    return dist(RNG);
}

static uint32_t NextPoll()
{
    std::uniform_int_distribution<uint32_t> dist(1, ~0U);
    return dist(RNG);
}

static void InitBuildKey()
{
    std::uniform_int_distribution<uint64_t> dist(1, ~0ULL);
    BuildKey = dist(RNG);
}

static uint64_t HashReg(uint64_t a)
{
    uint64_t x = a + HashGolden;
    x = (x << 23) | (x >> 41);
    x *= HashMix;
    x ^= x >> 32;
    return x;
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

static bool HasCFGNanoOptIn(Function& f)
{
    if (HasAnnotationTag(f, "cfgnano")) return true;
    if (HasAnnotationTag(f, "obfus") && IsAssignedToPass(f, "cfgnano")) return true;
    return false;
}

static bool HasCFGNanoOptOut(Function& f)
{
    return HasAnnotationTag(f, "nocfgnano") || HasAnnotationTag(f, "noobfus");
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

static bool HarvestDominatingConst(BranchInst* br, DominatorTree& dt, uint32_t& outval)
{
    DenseSet<uint32_t> seen;
    bool found = false;
    auto take = [&](Value* v)
    {
        if (found) return;
        auto* ci = dyn_cast<ConstantInt>(v);
        if (!ci) return;
        if (ci->getBitWidth() > 32) return;
        uint32_t x = (uint32_t)ci->getZExtValue();
        if (x == 0 || x == 1 || x == ~0U) return;
        if (!seen.insert(x).second) return;
        outval = x;
        found = true;
    };
    auto scan = [&](BasicBlock* bb)
    {
        for (Instruction& i : *bb)
        {
            for (Value* op : i.operands())
            {
                take(op);
                if (found) return;
            }
        }
    };
    scan(br->getParent());
    if (!found)
    {
        DomTreeNode* node = dt.getNode(br->getParent());
        unsigned depth = 0;
        while (!found && node && depth < HarvestDepth)
        {
            node = node->getIDom();
            if (!node) break;
            BasicBlock* bb = node->getBlock();
            if (!bb) break;
            scan(bb);
            ++depth;
        }
    }
    return found;
}

static InlineAsm* BuildSiteAsm(LLVMContext& c, unsigned slot, uint32_t poll)
{
    FunctionType* ty = FunctionType::get(Type::getVoidTy(c), {}, false);
    char buf[768];
    std::snprintf(buf, sizeof(buf),
        "mov rcx, qword ptr [rip + __cfgnano_fake_object_ptr]\n"
        "mov rax, qword ptr [rcx]\n"
        "mov rax, qword ptr [rax + %u]\n"
        "mov edx, 0x%08x\n"
        "call qword ptr [rip + __guard_dispatch_icall_fptr]",
        slot * 8u, poll);
    return InlineAsm::get(ty, buf,
        "~{rax},~{rcx},~{rdx},~{r8},~{r9},~{r10},~{r11},~{memory},~{dirflag},~{fpsr},~{flags}",
        true, false, InlineAsm::AD_Intel);
}

static void EmitSite(Function& f, BranchInst* br, DominatorTree& dt)
{
    LLVMContext& c = f.getContext();
    BasicBlock* target = br->getSuccessor(0);

    uint32_t poll = 0;
    bool pollfromharvest = false;
    if (Harvest)
    {
        if (HarvestDominatingConst(br, dt, poll))
            pollfromharvest = true;
    }
    if (poll == 0) poll = NextPoll();

    uint64_t sitekey = NextNonce();
    unsigned slot = (unsigned)SiteList.size();

    BasicBlock* landingbb = BasicBlock::Create(c, "CFGNanoLanding", &f, target);
    {
        IRBuilder<> b(landingbb);
        // landing BB must indirectbr to target so BlockAddress(F, target) stays valid; an unreachable terminator makes LLVM silently rewrite the BA to inttoptr(i64 1 to ptr) and poison the table bake
        Constant* targetba = BlockAddress::get(&f, target);
        IndirectBrInst* ibr = b.CreateIndirectBr(targetba, 1);
        ibr->addDestination(target);
    }

    {
        IRBuilder<> bp(br);
        bp.CreateCall(BuildSiteAsm(c, slot, poll));
    }
    br->setSuccessor(0, landingbb);
    ClaimNanomiteSite(br, "cfgnano");

    CFGNanoSite s;
    s.f = &f;
    s.landingbb = landingbb;
    s.targetbb = target;
    s.siteid = sitekey;
    s.poll = poll;
    s.pollfromharvest = pollfromharvest;
    s.vtslot = slot;
    SiteList.push_back(s);
}

static StructType* GetEntryType(LLVMContext& c)
{
    Type* i64 = Type::getInt64Ty(c);
    return StructType::get(c, {i64, i64, i64}, false);
}

static void EmitFakeVTablePlumbing(Module& m, ArrayRef<CFGNanoSite> sites)
{
    LLVMContext& c = m.getContext();
    PointerType* ptrty = PointerType::get(c, 0);
    IntegerType* i64 = Type::getInt64Ty(c);

    SmallVector<Constant*, 16> slotinits;
    slotinits.reserve(sites.size());
    for (const CFGNanoSite& s : sites)
    {
        Constant* keyint = ConstantInt::get(i64, s.siteid);
        Constant* keyptr = ConstantExpr::getIntToPtr(keyint, ptrty);
        slotinits.push_back(keyptr);
    }

    ArrayType* arrt = ArrayType::get(ptrty, slotinits.size());
    Constant* arr = ConstantArray::get(arrt, slotinits);
    auto* fakevtgv = new GlobalVariable(m, arrt, true, GlobalValue::ExternalLinkage, arr, "__cfgnano_fakevt");

    StructType* fakeobjt = StructType::get(c, {ptrty}, false);
    Constant* fakeobjinit = ConstantStruct::get(fakeobjt, {fakevtgv});
    auto* fakeobjgv = new GlobalVariable(m, fakeobjt, true, GlobalValue::ExternalLinkage, fakeobjinit, "__cfgnano_fake_object");

    (void)new GlobalVariable(m, ptrty, true, GlobalValue::ExternalLinkage, fakeobjgv, "__cfgnano_fake_object_ptr");
}

static GlobalVariable* EmitTable(Module& m, ArrayRef<CFGNanoSite> sites)
{
    LLVMContext& c = m.getContext();
    StructType* entryt = GetEntryType(c);
    IntegerType* i64 = Type::getInt64Ty(c);

    SmallVector<Constant*, 4> entries;
    entries.reserve(sites.size() + 1);
    for (const CFGNanoSite& s : sites)
    {
        Constant* keyc = ConstantInt::get(i64, s.siteid);
        Constant* targetba = BlockAddress::get(s.f, s.targetbb);
        Constant* targetint = ConstantExpr::getPtrToInt(targetba, i64);
        uint64_t h = HashReg((uint64_t)s.poll);
        uint64_t mask = h ^ BuildKey ^ s.siteid;
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enctarget = ConstantExpr::getAdd(targetint, maskc);
        Constant* siteidc = ConstantInt::get(i64, s.siteid);
        entries.push_back(ConstantStruct::get(entryt, {keyc, enctarget, siteidc}));
    }
    entries.push_back(ConstantStruct::get(entryt, {
        ConstantInt::get(i64, 0),
        ConstantInt::get(i64, 0),
        ConstantInt::get(i64, 0)
    }));

    ArrayType* arrt = ArrayType::get(entryt, entries.size());
    Constant* init = ConstantArray::get(arrt, entries);
    return new GlobalVariable(m, arrt, false, GlobalValue::ExternalLinkage, init, "__cfgnano_table");
}

static GlobalVariable* EmitBuildKeyGlobal(Module& m)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);
    return new GlobalVariable(m, i64, true, GlobalValue::ExternalLinkage, ConstantInt::get(i64, BuildKey), "__cfgnano_build_key");
}

static GlobalVariable* EmitPrevDispatcherGlobal(Module& m)
{
    LLVMContext& c = m.getContext();
    PointerType* ptrty = PointerType::get(c, 0);
    return new GlobalVariable(m, ptrty, false, GlobalValue::ExternalLinkage, ConstantPointerNull::get(ptrty), "__cfgnano_prev_dispatcher");
}

static GlobalVariable* DeclareCFGFptrGlobal(Module& m)
{
    if (auto* existing = m.getNamedGlobal("__guard_dispatch_icall_fptr")) return existing;
    LLVMContext& c = m.getContext();
    PointerType* ptrty = PointerType::get(c, 0);
    return new GlobalVariable(m, ptrty, false, GlobalValue::ExternalLinkage, nullptr, "__guard_dispatch_icall_fptr");
}

static Function* EmitDispatcher(Module& m)
{
    LLVMContext& c = m.getContext();
    FunctionType* ft = FunctionType::get(Type::getVoidTy(c), {}, false);
    Function* f = Function::Create(ft, GlobalValue::ExternalLinkage, "__cfgnano_dispatch", &m);
    f->addFnAttr(Attribute::Naked);
    f->addFnAttr(Attribute::NoInline);
    f->addFnAttr(Attribute::NoUnwind);
    f->setDLLStorageClass(GlobalValue::DefaultStorageClass);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    IRBuilder<> b(entry);

    const char* asmbody =
        "push r10\n"
        "push r11\n"
        "mov r10, rax\n"
        "lea r11, [rip + __cfgnano_table]\n"
        ".Lcfgnano_scan:\n"
        "mov rax, qword ptr [r11]\n"
        "test rax, rax\n"
        "jz .Lcfgnano_miss\n"
        "cmp rax, r10\n"
        "je .Lcfgnano_hit\n"
        "add r11, 24\n"
        "jmp .Lcfgnano_scan\n"
        ".Lcfgnano_hit:\n"
        "mov rax, 0xBF58476D1CE4E5B9\n"
        "add rax, rdx\n"
        "rol rax, 23\n"
        "mov r10, 0x94D049BB133111EB\n"
        "imul rax, r10\n"
        "mov r10, rax\n"
        "shr r10, 32\n"
        "xor rax, r10\n"
        "xor rax, qword ptr [rip + __cfgnano_build_key]\n"
        "xor rax, qword ptr [r11 + 16]\n"
        "mov r10, qword ptr [r11 + 8]\n"
        "sub r10, rax\n"
        "mov rax, r10\n"
        "pop r11\n"
        "pop r10\n"
        "add rsp, 8\n"
        "jmp rax\n"
        ".Lcfgnano_miss:\n"
        "mov rax, r10\n"
        "pop r11\n"
        "pop r10\n"
        "jmp qword ptr [rip + __cfgnano_prev_dispatcher]\n";

    InlineAsm* asmobj = InlineAsm::get(ft, asmbody, "", true, false, InlineAsm::AD_Intel);
    b.CreateCall(asmobj);
    b.CreateUnreachable();
    return f;
}

static Function* GetOrDeclareGMHA(Module& m)
{
    const char* name = "GetModuleHandleA";
    if (Function* existing = m.getFunction(name)) return existing;
    LLVMContext& c = m.getContext();
    PointerType* ptrty = PointerType::get(c, 0);
    FunctionType* ty = FunctionType::get(ptrty, {ptrty}, false);
    Function* f = Function::Create(ty, GlobalValue::ExternalLinkage, name, &m);
    f->setDLLStorageClass(GlobalValue::DLLImportStorageClass);
    f->addFnAttr(Attribute::NoUnwind);
    return f;
}

static Function* GetOrDeclareGPA(Module& m)
{
    const char* name = "GetProcAddress";
    if (Function* existing = m.getFunction(name)) return existing;
    LLVMContext& c = m.getContext();
    PointerType* ptrty = PointerType::get(c, 0);
    FunctionType* ty = FunctionType::get(ptrty, {ptrty, ptrty}, false);
    Function* f = Function::Create(ty, GlobalValue::ExternalLinkage, name, &m);
    f->setDLLStorageClass(GlobalValue::DLLImportStorageClass);
    f->addFnAttr(Attribute::NoUnwind);
    return f;
}

static GlobalVariable* MakeCStringGV(Module& m, StringRef s, const Twine& name)
{
    LLVMContext& c = m.getContext();
    Constant* init = ConstantDataArray::getString(c, s, true);
    auto* gv = new GlobalVariable(m, init->getType(), true, GlobalValue::PrivateLinkage, init, name);
    gv->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    gv->setAlignment(Align(1));
    return gv;
}

static Function* EmitInit(Module& m, Function* dispatcher, GlobalVariable* prevgv, GlobalVariable* cfgfptrgv)
{
    const char* name = "__cfgnano_init";
    if (Function* existing = m.getFunction(name)) return existing;

    LLVMContext& c = m.getContext();
    Type* voidt = Type::getVoidTy(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);

    GlobalVariable* strk32 = MakeCStringGV(m, "kernel32.dll", ".str.cfgnano.k32");
    GlobalVariable* strvp = MakeCStringGV(m, "VirtualProtect", ".str.cfgnano.vp");

    Function* gmh = GetOrDeclareGMHA(m);
    Function* gpa = GetOrDeclareGPA(m);

    FunctionType* vpty = FunctionType::get(i32, {ptrty, i64, i32, ptrty}, false);
    FunctionType* ft = FunctionType::get(voidt, {}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::NoUnwind);

    BasicBlock* bbentry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* bbgotk32 = BasicBlock::Create(c, "GotK32", f);
    BasicBlock* bbgotvp = BasicBlock::Create(c, "GotVP", f);
    BasicBlock* bbprotok = BasicBlock::Create(c, "ProtOk", f);
    BasicBlock* bbdone = BasicBlock::Create(c, "Done", f);

    Value* oldslot = nullptr;
    Value* k32 = nullptr;
    {
        IRBuilder<> b(bbentry);
        oldslot = b.CreateAlloca(i32, nullptr, "OldProt");
        b.CreateStore(ConstantInt::get(i32, 0), oldslot);
        k32 = b.CreateCall(gmh, {strk32}, "K32");
        Value* isnull = b.CreateICmpEQ(k32, ConstantPointerNull::get(ptrty), "K32IsNull");
        b.CreateCondBr(isnull, bbdone, bbgotk32);
    }

    Value* vpraw = nullptr;
    {
        IRBuilder<> b(bbgotk32);
        vpraw = b.CreateCall(gpa, {k32, strvp}, "VPRaw");
        Value* isnull = b.CreateICmpEQ(vpraw, ConstantPointerNull::get(ptrty), "VPIsNull");
        b.CreateCondBr(isnull, bbdone, bbgotvp);
    }

    {
        IRBuilder<> b(bbgotvp);
        Value* curdisp = b.CreateLoad(ptrty, cfgfptrgv, "CurDisp");
        b.CreateStore(curdisp, prevgv);
        Value* vpok = b.CreateCall(vpty, vpraw, {
            cfgfptrgv,
            ConstantInt::get(i64, 8),
            ConstantInt::get(i32, 0x04),
            oldslot
        }, "VPOk1");
        Value* ok = b.CreateICmpNE(vpok, ConstantInt::get(i32, 0), "VPOk1Bool");
        b.CreateCondBr(ok, bbprotok, bbdone);
    }

    {
        IRBuilder<> b(bbprotok);
        b.CreateStore(dispatcher, cfgfptrgv);
        Value* oldprot = b.CreateLoad(i32, oldslot, "OldVal");
        b.CreateCall(vpty, vpraw, {
            cfgfptrgv,
            ConstantInt::get(i64, 8),
            oldprot,
            oldslot
        });
        b.CreateBr(bbdone);
    }

    {
        IRBuilder<> b(bbdone);
        b.CreateRetVoid();
    }
    return f;
}

static bool EmitPlumbing(Module& m, ArrayRef<CFGNanoSite> sites)
{
    if (m.getFunction("__cfgnano_dispatch")) return false;
    if (sites.empty()) return false;
    // fakevt plumbing MUST land before dispatcher/init emission so the three symbols site asm references (__cfgnano_fake_object_ptr, __cfgnano_fake_object, __cfgnano_fakevt) exist in the module when the linker resolves the asm's RIP relative references
    EmitFakeVTablePlumbing(m, sites);
    (void)EmitBuildKeyGlobal(m);
    (void)EmitTable(m, sites);
    GlobalVariable* prevgv = EmitPrevDispatcherGlobal(m);
    GlobalVariable* cfgfptrgv = DeclareCFGFptrGlobal(m);
    Function* dispatch = EmitDispatcher(m);
    Function* init = EmitInit(m, dispatch, prevgv, cfgfptrgv);
    appendToGlobalCtors(m, init, 65535);
    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (f.getName().starts_with("__cfgnano_")) return false;
    if (HasCFGNanoOptOut(f)) return false;
    if (!HasCFGNanoOptIn(f)) return false;

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

bool RunCFGNano(Module& m)
{
    if (!CFGNanoEnable) return false;
    SiteList.clear();
    InitBuildKey();
    bool mutated = false;
    for (Function& f : m)
        mutated |= ProcessFunction(f);
    if (!SiteList.empty())
        mutated |= EmitPlumbing(m, SiteList);
    return mutated;
}

PreservedAnalyses CFGNanoPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunCFGNano(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}