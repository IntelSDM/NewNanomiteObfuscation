#pragma once

namespace llvm { class BranchInst; class Function; }

bool IsNanomiteClaimed(llvm::BranchInst* br);
void ClaimNanomiteSite(llvm::BranchInst* br, const char* pass);
bool IsAssignedToPass(llvm::Function& f, const char* pass);