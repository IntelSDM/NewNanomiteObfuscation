#include "NanomiteCommon.h"

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"

#include <cstring>

using namespace llvm;

static constexpr const char* ClaimKind = "nanomite.claimed";
static constexpr const char* Buckets[] = {"exnano", "icnano", "cfgnano"};

static uint64_t FNV1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

bool IsNanomiteClaimed(BranchInst* br)
{
    return br->getMetadata(ClaimKind) != nullptr;
}

void ClaimNanomiteSite(BranchInst* br, const char* pass)
{
    LLVMContext& c = br->getContext();
    MDString* tag = MDString::get(c, pass);
    Metadata* mds[] = { tag };
    MDNode* node = MDNode::get(c, mds);
    br->setMetadata(ClaimKind, node);
}

bool IsAssignedToPass(Function& f, const char* pass)
{
    uint64_t h = FNV1a64Range(f.getName());
    return strcmp(Buckets[h % 3], pass) == 0;
}