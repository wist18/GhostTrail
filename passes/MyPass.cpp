#ifndef MY_PASS_CXX
#define MY_PASS_CXX

#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
class MyPass : public PassInfoMixin<MyPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
    if (F.hasFnAttribute(Attribute::OptimizeNone)) {
      errs() << "MyPass is skipping function: " << F.getName() << " due to optnone attribute\n";
      return PreservedAnalyses::all();
    }
    errs() << "MyPass is running on function: " << F.getName() << "\n";
    // Your pass logic here
    return PreservedAnalyses::all();
  }
};
} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "MyPass", LLVM_VERSION_STRING, [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "my-pass") {
                    FPM.addPass(MyPass());
                    return true;
                  }
                  return false;
                });
          }};
}

#endif // MY_PASS_CXX
