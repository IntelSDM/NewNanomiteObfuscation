#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

#include "ExNanoPass.h"
#include "ICNanoPass.h"
#include "CFGNanoPass.h"
#include "llvm/IR/InlineAsm.h"

#include <ctime>
#include <cstdlib>

using namespace llvm;


struct ObfuscationPass : PassInfoMixin<ObfuscationPass>
{
    PreservedAnalyses run(Module& m, ModuleAnalysisManager&)
    {

        ExNanoEnable = true;
        ICNanoEnable = true;
        CFGNanoEnable = true;
        return PreservedAnalyses::none();
    }
};

llvm::PassPluginLibraryInfo GetPassPluginInfo()
{
    return
    {
        LLVM_PLUGIN_API_VERSION,
        "NanomitePass",
        LLVM_VERSION_STRING,
        [](PassBuilder& pb)
        {
            pb.registerOptimizerLastEPCallback([](ModulePassManager& pm, OptimizationLevel)
            {
                pm.addPass(ExNanoPass());
                pm.addPass(ICNanoPass());
                pm.addPass(CFGNanoPass());
            });
        }
    };
}
#ifndef LLVM_BYE_LINK_INTO_TOOLS
extern "C"
__declspec(dllexport) LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
#ifdef _WIN32
#endif
    srand(time(0));
    return GetPassPluginInfo();
}
#endif