#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct ICNanoPass : llvm::PassInfoMixin<ICNanoPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunICNano(llvm::Module& m);

extern llvm::cl::opt<bool> ICNanoEnable;