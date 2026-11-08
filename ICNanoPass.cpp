#include "ICNanoPass.h"
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

#include <cinttypes>
#include <cstdio>
#include <cstring>
#include <random>
#include <vector>

using namespace llvm;

cl::opt<bool> ICNanoEnable("obficnano", cl::init(true), cl::desc("Enables Instrument Callback (syscall) Nanomites"));

static constexpr unsigned MinSites = 1;
static constexpr bool SkipLoops = true;
static constexpr unsigned MaxSitesPerFn = 32;
static constexpr bool Harvest = true;
static constexpr unsigned HarvestDepth = 8;

static constexpr uint64_t HashGolden = 0x9E3779B97F4A7C15ULL;
static constexpr uint64_t HashMix = 0xC6BC279692B5C323ULL;

struct ICNanoSite
{
    Function* f;
    BasicBlock* landingbb;
    BasicBlock* targetbb;
    uint64_t siteid;
    uint64_t poll1;
    uint64_t poll2;
    bool p1fromharvest = false;
    bool p2fromharvest = false;
};

static std::vector<ICNanoSite> SiteList;
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

static uint64_t HashRegs(uint64_t a, uint64_t b)
{
    uint64_t x = a + HashGolden;
    x ^= b;
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

static bool HasICNanoOptIn(Function& f)
{
    if (HasAnnotationTag(f, "icnano")) return true;
    if (HasAnnotationTag(f, "obfus") && IsAssignedToPass(f, "icnano")) return true;
    return false;
}

static bool HasICNanoOptOut(Function& f)
{
    return HasAnnotationTag(f, "noicnano") || HasAnnotationTag(f, "noobfus");
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

static InlineAsm* BuildSiteAsm(LLVMContext& c, uint64_t poll1, uint64_t poll2)
{
    FunctionType* ty = FunctionType::get(Type::getVoidTy(c), {}, false);
    char buf[512];
    std::snprintf(buf, sizeof(buf),
        "mov r12, 0x%016" PRIx64 "\n"
        "mov r13, 0x%016" PRIx64 "\n"
        "mov eax, dword ptr [rip + __icnano_ssn]\n"
        "syscall",
        poll1, poll2);
    return InlineAsm::get(ty, buf,
        "~{r12},~{r13},~{rax},~{rcx},~{r11},~{memory},~{dirflag},~{fpsr},~{flags}",
        true, false, InlineAsm::AD_Intel);
}

static void EmitSite(Function& f, BranchInst* br, DominatorTree& dt)
{
    LLVMContext& c = f.getContext();
    BasicBlock* target = br->getSuccessor(0);

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

    BasicBlock* landingbb = BasicBlock::Create(c, "ICNanoLanding", &f, target);
    {
        IRBuilder<> b(landingbb);
        // landing BB terminator must be indirectbr to target; BlockAddress of an unreachable BB is silently rewritten by LLVM to inttoptr(i64 1 to ptr), poisoning the table bake
        Constant* targetba = BlockAddress::get(&f, target);
        IndirectBrInst* ibr = b.CreateIndirectBr(targetba, 1);
        ibr->addDestination(target);
    }

    {
        IRBuilder<> bp(br);
        bp.CreateCall(BuildSiteAsm(c, poll1, poll2));
    }
    br->setSuccessor(0, landingbb);
    ClaimNanomiteSite(br, "icnano");

    ICNanoSite s;
    s.f = &f;
    s.landingbb = landingbb;
    s.targetbb = target;
    s.siteid = siteid;
    s.poll1 = poll1;
    s.poll2 = poll2;
    s.p1fromharvest = p1fromharvest;
    s.p2fromharvest = p2fromharvest;
    SiteList.push_back(s);
}

static StructType* GetEntryType(LLVMContext& c)
{
    return StructType::get(c, {PointerType::get(c, 0), Type::getInt64Ty(c), Type::getInt64Ty(c)}, false);
}

static GlobalVariable* EmitSSNGlobal(Module& m)
{
    if (GlobalVariable* existing = m.getNamedGlobal("__icnano_ssn")) return existing;
    LLVMContext& c = m.getContext();
    Type* i32 = Type::getInt32Ty(c);
    // ExternalLinkage so the per site inline asm can reference __icnano_ssn by name as a RIP-relative symbol
    return new GlobalVariable(m, i32, false, GlobalValue::ExternalLinkage, ConstantInt::get(i32, 0), "__icnano_ssn");
}

static GlobalVariable* EmitBuildKeyGlobal(Module& m)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);
    return new GlobalVariable(m, i64, true, GlobalValue::ExternalLinkage, ConstantInt::get(i64, BuildKey), "__icnano_build_key");
}

static GlobalVariable* EmitTable(Module& m, ArrayRef<ICNanoSite> sites)
{
    LLVMContext& c = m.getContext();
    StructType* entryt = GetEntryType(c);
    PointerType* ptrty = PointerType::get(c, 0);
    IntegerType* i64 = Type::getInt64Ty(c);

    SmallVector<Constant*, 4> entries;
    entries.reserve(sites.size() + 1);
    for (const ICNanoSite& s : sites)
    {
        Constant* landingba = BlockAddress::get(s.f, s.landingbb);
        Constant* targetba = BlockAddress::get(s.f, s.targetbb);
        Constant* targetint = ConstantExpr::getPtrToInt(targetba, i64);
        uint64_t h = HashRegs(s.poll1, s.poll2);
        uint64_t mask = h ^ BuildKey ^ s.siteid;
        Constant* maskc = ConstantInt::get(i64, mask);
        Constant* enctarget = ConstantExpr::getAdd(targetint, maskc);
        Constant* siteidc = ConstantInt::get(i64, s.siteid);
        entries.push_back(ConstantStruct::get(entryt, {landingba, enctarget, siteidc}));
    }
    entries.push_back(ConstantStruct::get(entryt, {
        ConstantPointerNull::get(ptrty),
        ConstantInt::get(i64, 0),
        ConstantInt::get(i64, 0)
    }));

    ArrayType* arrt = ArrayType::get(entryt, entries.size());
    Constant* init = ConstantArray::get(arrt, entries);
    return new GlobalVariable(m, arrt, false, GlobalValue::ExternalLinkage, init, "__icnano_table");
}

static Function* EmitDispatcher(Module& m)
{
    LLVMContext& c = m.getContext();
    FunctionType* ft = FunctionType::get(Type::getVoidTy(c), {}, false);
    Function* f = Function::Create(ft, GlobalValue::ExternalLinkage, "__icnano_dispatch", &m);
    f->addFnAttr(Attribute::Naked);
    f->addFnAttr(Attribute::NoInline);
    f->addFnAttr(Attribute::NoUnwind);
    f->setDLLStorageClass(GlobalValue::DefaultStorageClass);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", f);
    IRBuilder<> b(entry);

    const char* asmbody =
        "push rax\n"
        "push rbx\n"
        "lea rax, [rip + __icnano_table]\n"
        ".Licnano_scan:\n"
        "mov rbx, qword ptr [rax]\n"
        "test rbx, rbx\n"
        "jz .Licnano_miss\n"
        "cmp rbx, r10\n"
        "je .Licnano_hit\n"
        "add rax, 24\n"
        "jmp .Licnano_scan\n"
        ".Licnano_hit:\n"
        "mov rbx, 0x9E3779B97F4A7C15\n"
        "add rbx, r12\n"
        "xor rbx, r13\n"
        "rol rbx, 23\n"
        "mov rcx, 0xC6BC279692B5C323\n"
        "imul rbx, rcx\n"
        "mov rcx, rbx\n"
        "shr rcx, 32\n"
        "xor rbx, rcx\n"
        "xor rbx, qword ptr [rip + __icnano_build_key]\n"
        "xor rbx, qword ptr [rax + 16]\n"
        "mov rcx, qword ptr [rax + 8]\n"
        "sub rcx, rbx\n"
        "mov r10, rcx\n"
        ".Licnano_miss:\n"
        "pop rbx\n"
        "pop rax\n"
        "jmp r10\n";

    InlineAsm* asmobj = InlineAsm::get(ft, asmbody, "", true, false, InlineAsm::AD_Intel);
    b.CreateCall(asmobj);
    b.CreateUnreachable();
    return f;
}

static Function* GetOrDeclareGetModuleHandleA(Module& m)
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

static Function* GetOrDeclareGetProcAddress(Module& m)
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

static Function* EmitInit(Module& m, Function* dispatcher, GlobalVariable* ssngv)
{
    const char* name = "__icnano_init";
    if (Function* existing = m.getFunction(name)) return existing;

    LLVMContext& c = m.getContext();
    Type* voidt = Type::getVoidTy(c);
    Type* i8 = Type::getInt8Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);

    GlobalVariable* strntdll = MakeCStringGV(m, "ntdll.dll", ".str.icnano.ntdll");
    GlobalVariable* strnyex = MakeCStringGV(m, "NtYieldExecution", ".str.icnano.nyex");
    GlobalVariable* strnsip = MakeCStringGV(m, "NtSetInformationProcess", ".str.icnano.nsip");

    StructType* infot = StructType::get(c, {i32, i32, ptrty}, false);
    Constant* initinfo = ConstantStruct::get(infot, {
        ConstantInt::get(i32, 0),
        ConstantInt::get(i32, 0),
        dispatcher
    });
    auto* infogv = new GlobalVariable(m, infot, false, GlobalValue::InternalLinkage, initinfo, "__icnano_cbinfo");

    Function* gmh = GetOrDeclareGetModuleHandleA(m);
    Function* gpa = GetOrDeclareGetProcAddress(m);

    FunctionType* nsipty = FunctionType::get(i32, {ptrty, i32, ptrty, i32}, false);
    FunctionType* ft = FunctionType::get(voidt, {}, false);
    Function* f = Function::Create(ft, GlobalValue::InternalLinkage, name, &m);
    f->addFnAttr(Attribute::NoUnwind);

    BasicBlock* bbentry = BasicBlock::Create(c, "Entry", f);
    BasicBlock* bbgotntdll = BasicBlock::Create(c, "GotNtdll", f);
    BasicBlock* bbgotstub = BasicBlock::Create(c, "GotStub", f);
    BasicBlock* bbscanouter = BasicBlock::Create(c, "ScanOuter", f);
    BasicBlock* bbcheckb8 = BasicBlock::Create(c, "CheckB8", f);
    BasicBlock* bbhaveb8 = BasicBlock::Create(c, "HaveB8", f);
    BasicBlock* bbscaninner = BasicBlock::Create(c, "ScanInner", f);
    BasicBlock* bbcheck0f = BasicBlock::Create(c, "Check0F", f);
    BasicBlock* bbcheck05 = BasicBlock::Create(c, "Check05", f);
    BasicBlock* bbinnercont = BasicBlock::Create(c, "InnerCont", f);
    BasicBlock* bboutercont = BasicBlock::Create(c, "OuterCont", f);
    BasicBlock* bbfound = BasicBlock::Create(c, "Found", f);
    BasicBlock* bbgotnsip = BasicBlock::Create(c, "GotNsip", f);
    BasicBlock* bbdone = BasicBlock::Create(c, "Done", f);

    Value* ntdll = nullptr;
    {
        IRBuilder<> b(bbentry);
        ntdll = b.CreateCall(gmh, {strntdll}, "Ntdll");
        Value* isnull = b.CreateICmpEQ(ntdll, ConstantPointerNull::get(ptrty), "NtdllIsNull");
        b.CreateCondBr(isnull, bbdone, bbgotntdll);
    }

    Value* stub = nullptr;
    {
        IRBuilder<> b(bbgotntdll);
        stub = b.CreateCall(gpa, {ntdll, strnyex}, "Stub");
        Value* isnull = b.CreateICmpEQ(stub, ConstantPointerNull::get(ptrty), "StubIsNull");
        b.CreateCondBr(isnull, bbdone, bbgotstub);
    }

    {
        IRBuilder<> b(bbgotstub);
        b.CreateBr(bbscanouter);
    }

    PHINode* iphi = nullptr;
    {
        IRBuilder<> b(bbscanouter);
        iphi = b.CreatePHI(i32, 2, "I");
        iphi->addIncoming(ConstantInt::get(i32, 0), bbgotstub);
        Value* iatend = b.CreateICmpUGE(iphi, ConstantInt::get(i32, 32), "IAtEnd");
        b.CreateCondBr(iatend, bbdone, bbcheckb8);
    }

    {
        IRBuilder<> b(bbcheckb8);
        Value* i64v = b.CreateZExt(iphi, i64);
        Value* pi = b.CreateGEP(i8, stub, i64v, "PI");
        Value* bi = b.CreateLoad(i8, pi, "BI");
        Value* isb8 = b.CreateICmpEQ(bi, ConstantInt::get(i8, (int8_t)0xB8), "IsB8");
        b.CreateCondBr(isb8, bbhaveb8, bboutercont);
    }

    Value* candssn = nullptr;
    Value* jstart = nullptr;
    {
        IRBuilder<> b(bbhaveb8);
        Value* iplus1 = b.CreateAdd(iphi, ConstantInt::get(i32, 1));
        Value* iplus164 = b.CreateZExt(iplus1, i64);
        Value* ssnp = b.CreateGEP(i8, stub, iplus164, "SSNP");
        candssn = b.CreateLoad(i32, ssnp, "CandSSN");
        jstart = b.CreateAdd(iphi, ConstantInt::get(i32, 5), "JStart");
        b.CreateBr(bbscaninner);
    }

    PHINode* jphi = nullptr;
    {
        IRBuilder<> b(bbscaninner);
        jphi = b.CreatePHI(i32, 2, "J");
        jphi->addIncoming(jstart, bbhaveb8);
        Value* jlimit = b.CreateAdd(iphi, ConstantInt::get(i32, 32), "JLimit");
        Value* jatend = b.CreateICmpUGE(jphi, jlimit, "JAtEnd");
        b.CreateCondBr(jatend, bboutercont, bbcheck0f);
    }

    {
        IRBuilder<> b(bbcheck0f);
        Value* j64 = b.CreateZExt(jphi, i64);
        Value* pj = b.CreateGEP(i8, stub, j64, "PJ");
        Value* bj = b.CreateLoad(i8, pj, "BJ");
        Value* is0f = b.CreateICmpEQ(bj, ConstantInt::get(i8, 0x0F), "Is0F");
        b.CreateCondBr(is0f, bbcheck05, bbinnercont);
    }

    {
        IRBuilder<> b(bbcheck05);
        Value* jplus1 = b.CreateAdd(jphi, ConstantInt::get(i32, 1));
        Value* jplus164 = b.CreateZExt(jplus1, i64);
        Value* pj1 = b.CreateGEP(i8, stub, jplus164, "PJ1");
        Value* bj1 = b.CreateLoad(i8, pj1, "BJ1");
        Value* is05 = b.CreateICmpEQ(bj1, ConstantInt::get(i8, 0x05), "Is05");
        b.CreateCondBr(is05, bbfound, bbinnercont);
    }

    {
        IRBuilder<> b(bbinnercont);
        Value* jnext = b.CreateAdd(jphi, ConstantInt::get(i32, 1), "JNext");
        jphi->addIncoming(jnext, bbinnercont);
        b.CreateBr(bbscaninner);
    }

    {
        IRBuilder<> b(bboutercont);
        Value* inext = b.CreateAdd(iphi, ConstantInt::get(i32, 1), "INext");
        iphi->addIncoming(inext, bboutercont);
        b.CreateBr(bbscanouter);
    }

    Value* nsip = nullptr;
    {
        IRBuilder<> b(bbfound);
        b.CreateStore(candssn, ssngv);
        nsip = b.CreateCall(gpa, {ntdll, strnsip}, "Nsip");
        Value* isnull = b.CreateICmpEQ(nsip, ConstantPointerNull::get(ptrty), "NsipIsNull");
        b.CreateCondBr(isnull, bbdone, bbgotnsip);
    }

    {
        IRBuilder<> b(bbgotnsip);
        Value* hcur = b.CreateIntToPtr(ConstantInt::get(i64, (uint64_t)-1LL), ptrty, "HCur");
        unsigned infosize = (unsigned)m.getDataLayout().getTypeAllocSize(infot);
        b.CreateCall(nsipty, nsip, {
            hcur,
            ConstantInt::get(i32, 40),
            infogv,
            ConstantInt::get(i32, infosize)
        });
        b.CreateBr(bbdone);
    }

    {
        IRBuilder<> b(bbdone);
        b.CreateRetVoid();
    }
    return f;
}

static bool EmitPlumbing(Module& m, ArrayRef<ICNanoSite> sites)
{
    if (m.getFunction("__icnano_dispatch")) return false;
    if (sites.empty()) return false;
    GlobalVariable* ssngv = EmitSSNGlobal(m);
    (void)EmitBuildKeyGlobal(m);
    (void)EmitTable(m, sites);
    Function* dispatch = EmitDispatcher(m);
    Function* init = EmitInit(m, dispatch, ssngv);
    appendToGlobalCtors(m, init, 65535);
    return true;
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (f.getName().starts_with("__icnano_")) return false;
    if (HasICNanoOptOut(f)) return false;
    if (!HasICNanoOptIn(f)) return false;

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

bool RunICNano(Module& m)
{
    if (!ICNanoEnable) return false;
    SiteList.clear();
    InitBuildKey();
    bool mutated = false;
    for (Function& f : m)
        mutated |= ProcessFunction(f);
    if (!SiteList.empty())
        mutated |= EmitPlumbing(m, SiteList);
    return mutated;
}

PreservedAnalyses ICNanoPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunICNano(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}