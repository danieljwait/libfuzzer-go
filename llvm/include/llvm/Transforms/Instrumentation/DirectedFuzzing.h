//===--------- Definition of the SanitizerCoverage class --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// DirectedFuzzing is //TODO: Add description here
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_INSTRUMENTATION_DIRECTEDFUZZING_H
#define LLVM_TRANSFORMS_INSTRUMENTATION_DIRECTEDFUZZING_H

#include "llvm/IR/PassManager.h"

namespace llvm {

/// The instrumentation pass for TODO: Add description here
class DirectedFuzzingPass : public PassInfoMixin<DirectedFuzzingPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_INSTRUMENTATION_DIRECTEDFUZZING_H