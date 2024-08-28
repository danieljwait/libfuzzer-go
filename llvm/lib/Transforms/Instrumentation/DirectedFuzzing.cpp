
//===-- DirectedFuzzing.cpp - TODO: description ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// TODO: Add description here
//
//===----------------------------------------------------------------------===//

#include <fstream>
#include <iostream>
#include <list>
#include <map>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/EHPersonalities.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Instrumentation/DirectedFuzzing.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#define KNRM  "\x1B[0m"
#define KRED  "\x1B[31m"
#define KGRN  "\x1B[32m"
#define KYEL  "\x1B[33m"
#define KBLU  "\x1B[34m"
#define KMAG  "\x1B[35m"
#define KCYN  "\x1B[36m"
#define KWHT  "\x1B[37m"
using namespace llvm;

static cl::opt<std::string> DistanceFile(
    "distance",
    cl::desc("Distance file containing the distance of each basic block to the provided targets."),
    cl::value_desc("filename")
);

std::string AccumulatorName = "__libfuzzer_directed_accumulator";
std::string CounterName = "__libfuzzer_directed_counter";
std::map<std::string, int> BBDistances;

bool LoadBBDistances(void) {
  if (DistanceFile.empty()) {
    return false;
  }

  std::ifstream DistanceStream(DistanceFile);
  if (!DistanceStream.is_open()) {
    return false;
  }

  std::string Line;
  while (getline(DistanceStream, Line)) {
    std::size_t Pos = Line.find(",");
    std::string BBName = Line.substr(0, Pos);
    int BBDist = (int) (100.0 * atof(Line.substr(Pos + 1, Line.length()).c_str()));
    BBDistances.emplace(BBName, BBDist);
  }
  DistanceStream.close();

  // DEBUG Print the contents of distance.cfg.txt
  if (false) {
    llvm::errs() << "Parsed contents of distance.cfg.txt:\n";
    for (auto &BBDist : BBDistances) {
      llvm::errs() << "\t" << BBDist.first << " - " << BBDist.second << "\n";
    }
    llvm::errs() << "\n";
  }

  return true;
}

void GetOrCreateGlobalVariables(Module &M) {
  LLVMContext *C = &(M.getContext());
  IRBuilder<> IRB(*C);
  IntegerType *Int64Ty = IRB.getInt64Ty();

  auto MakeVariable = [&](const std::string &Name) {
    M.getOrInsertGlobal(Name, Int64Ty);
    GlobalVariable *Var = M.getNamedGlobal(Name);
    Var->setLinkage(GlobalValue::ExternalLinkage);
    if (M.getFunction("LLVMFuzzerTestOneInput")) {
      Var->setInitializer(IRB.getInt64(0));
    }
    Var->setConstant(false);
  };

  MakeVariable(AccumulatorName);
  MakeVariable(CounterName);
}

std::string GetBBName(BasicBlock &BB) {
  std::string BBName;
  for (auto &Inst : BB) {
    llvm::DebugLoc Loc = Inst.getDebugLoc();
    if (!Loc.get())
      continue;

    int Line = Loc->getLine();
    llvm::StringRef Filename = Loc->getFilename();
    if (Filename.empty() || Line == 0)
      continue;

    std::size_t Pos = Filename.find_last_of("/\\");
    if (Pos != std::string::npos)
      Filename = Filename.substr(Pos + 1);
    BBName = Filename.str() + ":" + std::to_string(Line);
    break;
  }

  // DEBUG Print the BBName and the distance
  if (false) {
    if (!BBName.empty()) {
        if (BBDistances.find(BBName) != BBDistances.end()) {
          int Distance = BBDistances[BBName];
          llvm::errs() << "\t" << BBName << " - " << Distance << "\n";
        }
        else {
          llvm::errs() << "\t" << BBName << " - unknown distance\n";
        }
    }
  }

  return BBName;
}

void InstrumentBB(BasicBlock &BB, std::string BBName) {
  BasicBlock::iterator IP = BB.getFirstInsertionPt();
  IRBuilder<> IRB(&*IP);
  IntegerType *Int64Ty = IRB.getInt64Ty();

  auto AddToVar = [&](const std::string &VarName, int Value) {
    GlobalVariable *Var = BB.getModule()->getNamedGlobal(VarName);
    auto Load = IRB.CreateLoad(Int64Ty, Var);
    auto Add = IRB.CreateAdd(Load, ConstantInt::get(Int64Ty, Value));
    IRB.CreateStore(Add, Var);
  };

  AddToVar(AccumulatorName, BBDistances[BBName]);
  AddToVar(CounterName, 1);
}

PreservedAnalyses DirectedFuzzingPass::run(Module &M, ModuleAnalysisManager &MAM) {
  if (!LoadBBDistances()) {
    llvm::errs() << "Failed to load basic block distances\n";
    return PreservedAnalyses::none();
  }

  GetOrCreateGlobalVariables(M);

  int total = 0;
  int instrumented = 0;

  for (auto& F : M) {
    for (auto& BB : F) {
      std::string BBName = GetBBName(BB);
      if (!BBName.empty() && BBDistances.find(BBName) != BBDistances.end()) {
        InstrumentBB(BB, BBName);
        instrumented++;
      }
      total++;
    }
  }

  if (instrumented != 0) {
    llvm::outs() << "Instrumented: " << instrumented << " / " << total << " in " << M.getSourceFileName() << "\n";
  } else {
    llvm::outs() << "No basic blocks instrumented in " << M.getSourceFileName() << "\n";
  }

  return PreservedAnalyses::none();
}















// ------------------------- AFLGo Pre-Processing Port -------------------------
// 
// cl::opt<std::string> TargetsFile(
//     "targets",
//     cl::desc("Input file containing the target lines of code."),
//     cl::value_desc("targets"));
// 
// cl::opt<std::string> OutDirectory(
//     "outdir",
//     cl::desc("Output directory where Ftargets.txt, Fnames.txt, and BBnames.txt are generated."),
//     cl::value_desc("outdir"));
// 
// namespace llvm {
// 
// template<>
// struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits {
//   DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}
// 
//   static std::string getGraphName(Function *F) {
//     return "CFG for '" + F->getName().str() + "' function";
//   }
// 
//   std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
//     if (!Node->getName().empty()) {
//       return Node->getName().str();
//     }
// 
//     std::string Str;
//     raw_string_ostream OS(Str);
// 
//     Node->printAsOperand(OS, false);
//     return OS.str();
//   }
// };
// 
// static void getDebugLoc(const Instruction *I, std::string &Filename,
//                         unsigned &Line) {
//   if (DILocation *Loc = I->getDebugLoc()) {
//     Line = Loc->getLine();
//     Filename = Loc->getFilename().str();
// 
//     if (Filename.empty()) {
//       DILocation *oDILoc = Loc->getInlinedAt();
//       if (oDILoc) {
//         Line = oDILoc->getLine();
//         Filename = oDILoc->getFilename().str();
//       }
//     }
//   }
// }
// 
// } // namespace llvm
// 
// static bool isBlacklisted(const Function *F) {
//   static const SmallVector<std::string, 8> Blacklist = {
//     "asan.",
//     "llvm.",
//     "sancov.",
//     "__ubsan_handle_",
//     "free",
//     "malloc",
//     "calloc",
//     "realloc"
//   };
// 
//   for (auto const &BlacklistFunc : Blacklist) {
//     if (F->getName().starts_with(BlacklistFunc)) {
//       return true;
//     }
//   }
// 
//   return false;
// }
// 
// PreservedAnalyses DirectedFuzzingPass::run(Module &M,
//                                              ModuleAnalysisManager &MAM) {
//   std::list<std::string> targets;
//   std::map<std::string, int> bb_to_dis;
//   std::vector<std::string> basic_blocks;
// 
//   if (!TargetsFile.empty()) {
// 
//     if (OutDirectory.empty()) {
//       assert(false && "Provide output directory '-outdir <directory>'");
//     }
// 
//     std::ifstream targetsfile(TargetsFile);
//     std::string line;
//     while (std::getline(targetsfile, line))
//       targets.push_back(line);
//     targetsfile.close();
//   }
// 
//   std::ofstream bbnames(OutDirectory + "/BBnames.txt", std::ofstream::out | std::ofstream::app);
//   std::ofstream bbcalls(OutDirectory + "/BBcalls.txt", std::ofstream::out | std::ofstream::app);
//   std::ofstream fnames(OutDirectory + "/Fnames.txt", std::ofstream::out | std::ofstream::app);
//   std::ofstream ftargets(OutDirectory + "/Ftargets.txt", std::ofstream::out | std::ofstream::app);
// 
//   /* Create dot-files directory */
//   std::string dotfiles(OutDirectory + "/dot-files");
//   if (sys::fs::create_directory(dotfiles)) {
//     assert(false && "Could not create directory.");
//   }
// 
//   for (auto &F : M) {
// 
//     bool has_BBs = false;
//     std::string funcName = F.getName().str();
// 
//     /* Black list of function names */
//     if (isBlacklisted(&F)) {
//       continue;
//     }
// 
//     bool is_target = false;
//     for (auto &BB : F) {
// 
//       std::string bb_name("");
//       std::string filename;
//       unsigned line;
// 
//       for (auto &I : BB) {
//         getDebugLoc(&I, filename, line);
// 
//         /* Don't worry about external libs */
//         static const std::string Xlibs("/usr/");
//         if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
//           continue;
// 
//         std::size_t found = filename.find_last_of("/\\");
//         if (found != std::string::npos)
//           filename = filename.substr(found + 1);
// 
//         if (bb_name.empty()) 
//           bb_name = filename + ":" + std::to_string(line);
//       
//         if (!is_target) {
//           for (auto &target : targets) {
//             std::size_t found = target.find_last_of("/\\");
//             if (found != std::string::npos)
//               target = target.substr(found + 1);
// 
//             std::size_t pos = target.find_last_of(":");
//             std::string target_file = target.substr(0, pos);
//             unsigned int target_line = atoi(target.substr(pos + 1).c_str());
//
//             if (!target_file.compare(filename) && target_line == line)
//               is_target = true;
//
//           }
//         }
//
//         if (auto *c = dyn_cast<CallInst>(&I)) {
//
//           std::size_t found = filename.find_last_of("/\\");
//           if (found != std::string::npos)
//             filename = filename.substr(found + 1);
//
//           if (auto *CalledF = c->getCalledFunction()) {
//             if (!isBlacklisted(CalledF))
//               bbcalls << bb_name << "," << CalledF->getName().str() << "\n";
//           }
//         }
//       }
//
//       if (!bb_name.empty()) {
//
//         BB.setName(bb_name + ":");
//         // if (!BB.hasName()) {
//         //   std::string newname = bb_name + ":";
//         //   Twine t(newname);
//         //   SmallString<256> NameData;
//         //   StringRef NameRef = t.toStringRef(NameData);
//         //   MallocAllocator Allocator;
//         //   BB.setValueName(ValueName::Create(NameRef, Allocator));
//         // }
//
//         bbnames << BB.getName().str() << "\n";
//         has_BBs = true;
//       }
//     }
//
//     if (has_BBs) {
//       /* Print CFG */
//       std::string cfgFileName = dotfiles + "/cfg." + funcName + ".dot";
//       std::error_code EC;
//       raw_fd_ostream cfgFile(cfgFileName, EC, sys::fs::OF_None);
//       if (!EC) {
//         WriteGraph(cfgFile, &F, true);
//       }
//
//       if (is_target)
//         ftargets << F.getName().str() << "\n";
//       fnames << F.getName().str() << "\n";
//     }
//   }
// 
//   return PreservedAnalyses::all();
// }