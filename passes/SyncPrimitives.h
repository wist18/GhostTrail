//===-- SyncPrimitives.h - Simple Sync Primitives Analysis ------*- C++ -*-===//
//
// Part of the VUsec Bsc. project on SCUAF.
// See SCUAF paper for reference (https://www.vusec.net/projects/ghostrace/).
// Author: Razvan Wist
// Supervisor: Cristiano Giuffrida
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_SYNCPRIMITIVES_H
#define LLVM_TRANSFORMS_UTILS_SYNCPRIMITIVES_H

#include "llvm/IR/CFG.h"  // For utility functions related to control flow
#include "llvm/IR/PassManager.h" // new PassManager(PM)
#include "llvm/IR/LLVMContext.h"
#include <llvm/IR/DerivedTypes.h>  // For PointerType
#include <llvm/IR/Function.h>
#include <llvm/IR/Type.h>
#include "llvm/IR/GlobalVariable.h"
#include "SyncPrimitives.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Support/FormatVariadic.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <queue>
#include <vector>
#include <string>
#include <algorithm> // Ensure to include for std::remove and std::erase

#define RED_START "\033[1;31m"
#define GREEN_START "\033[1;32m"
#define YELLOW_START "\033[1;33m"
#define BLUE_START "\033[1;34m"
#define COLOR_END "\033[0m"
#define SROA ".sroa"
#define ADDR ".addr"

#define VOID_TYPE_STRING "void"
#define INT_TYPE_STRING "int"
#define FLOATING_TYPE_STRING "floating_type"
#define FLOAT_TYPE_STRING "float"
#define DOUBLE_TYPE_STRING "double"
#define PTR_TYPE_STRING "ptr"
#define LITERAL_STRUCT_TYPE_STRING "literal_struct"
#define ARRAY_TYPE_STRING "array"
#define FUNCTION_TYPE_STRING "function"
#define TYPED_POINTER_TYPE_STRING "typed_ptr"
#define VECTOR_TYPE_STRING "vector"
#define UNKNOWN_TYPE_STRING "UnknownType"

#define REPORT_CLASS_GUARDED_FREE "guarded_free"
#define REPORT_CLASS_GUARDED_FREE_NULL "guarded_free_null"
#define REPORT_CLASS_GUARDED_FREE_VAL "guarded_free_val"
#define REPORT_CALSS_GUARDED_FREE_LIST_DEL "guarded_free_list_del"
#define REPORT_CLASS_FPTR_COPY "fptr_copy"
#define REPORT_CLASS_FPTR_CALL "fptr_call"

enum class Op { LOCK, UNLOCK, FREE, UPDATE_NULL, UPDATE_VAL, LISTDEL, FPTR_CALL, FPTR_COPY, UNKNOWN };

namespace llvm {

class SyncPrimitivesPass : public PassInfoMixin<SyncPrimitivesPass> {
public:
  PreservedAnalyses run(Module  &M, ModuleAnalysisManager &MAM);
};

struct StoreInstInfo {
    Op store_inst_type = Op::UNKNOWN;
    llvm::StoreInst* store_inst = nullptr;
    std::string operand_scope;
    std::vector<std::string> operand_type_list;
    std::vector<llvm::CallInst*> call_path;
    std::string call_path_string;

    void print(std::string report_class) const {
        errs() << llvm::formatv("\"report_class\": \"{0}\"", 
                    report_class);
        errs() << ", ";
        errs() << llvm::formatv("\"{0}_call_path\": \"{1}\"", 
                report_class,
                call_path_string);
        errs() << ", ";

        std::string typesStr = "";
        for (const auto& type : operand_type_list) {
            typesStr += "\"" + type + "\" ";
        }
        errs() << llvm::formatv("\"{0}_operand_scope\": \"{1}\", \"{0}_operand_type_list\": [ {2}]",
                    report_class,
                    operand_scope,
                    typesStr);
        errs() << ", ";
        /*

        // TODO

        if (store_inst) {
            llvm::DebugLoc debugLoc = store_inst->getDebugLoc();   // ERROR HERE
            std::string func_position;
            
            if (debugLoc) {
                if (auto *scope = llvm::dyn_cast<llvm::DIScope>(debugLoc->getScope())) {
                    func_position = scope->getFilename().str() + " +" + std::to_string(debugLoc.getLine());
                } else {
                    func_position = "(invalid-debug-scope)";
                }
            } else {
                func_position = "(no-debug-info)";
            }

            llvm::errs() << llvm::formatv("\"{0}_position\": \"{1}\"", 
                                        report_class,
                                        func_position) << "\n";
        }*/
    }    

    bool operator==(const StoreInstInfo& other) const {
        return call_path == other.call_path;
    }

    bool operator!=(const StoreInstInfo& other) const {
        return call_path != other.call_path;
    }
};

struct CallInstInfo {
    Op call_inst_type = Op::UNKNOWN;
    std::string operand_scope;
    std::vector<std::string> operand_type_list;
    std::vector<llvm::CallInst*> call_path;
    std::string call_path_string;
    
    void print(std::string report_class) const {
        errs() << llvm::formatv("\"report_class\": \"{0}\"", 
                    report_class);
        errs() << ", ";
        
        errs() << llvm::formatv("\"{0}_call_path\": \"{1}\"", 
                REPORT_CLASS_GUARDED_FREE,
                call_path_string);
        errs() << ", ";

        std::string typesStr = "";
        for (const auto& type : operand_type_list) {
            typesStr += "\"" + type + "\" ";
        }
        errs() << llvm::formatv("\"{0}_operand_scope\": \"{1}\", \"{0}_operand_type_list\": [ {2}]",
                    REPORT_CLASS_GUARDED_FREE,
                    operand_scope,
                    typesStr);
        errs() << ", ";

        std::string func_name = "unnamed_function";

        if (!call_path.empty() && call_path.back()) {
            
            /*

            // TODO

            auto *callOperand = call_path.back()->getCalledOperand();

            
            if (callOperand) {
                if (llvm::Value* value = dyn_cast<llvm::Value>(callOperand)) {
                    if (auto *loadInst = dyn_cast<llvm::LoadInst>(value)) {
                        if (loadInst->getPointerOperand()->hasName()) {
                            func_name = loadInst->getPointerOperand()->getName().str();
                        }
                    }
                }
            }

            auto *calledFunction = call_path.back()->getCalledFunction();

            if (calledFunction && calledFunction->hasName()) {
                func_name = calledFunction->getName().str();
            }

            */
            
            errs() << llvm::formatv("\"{0}_func\": \"{1}\"", 
                        REPORT_CLASS_GUARDED_FREE,
                        func_name);
            errs() << ", ";
        }


        
        /*

        // TODO

        if (call_path.back()) {
            llvm::DebugLoc debugLoc = call_path.back()->getDebugLoc();  // ERROR HERE
            std::string func_position;
            
            if (debugLoc) {
                if (auto *scope = llvm::dyn_cast<llvm::DIScope>(debugLoc->getScope())) {
                    func_position = scope->getFilename().str() + " +" + std::to_string(debugLoc.getLine());
                } else {
                    func_position = "(invalid-debug-scope)";
                }
            } else {
                func_position = "(no-debug-info)";
            }

            llvm::errs() << llvm::formatv("\"{0}_position\": \"{1}\"", 
                                        REPORT_CLASS_GUARDED_FREE,
                                        func_position) << "\n";
        }*/
    }    

    bool operator==(const CallInstInfo& other) const {
        return call_path == other.call_path;
    }

    bool operator!=(const CallInstInfo& other) const {
        return call_path != other.call_path;
    }
};

struct FreeGadget {
    std::string report_class = "undefined";
    CallInstInfo callInstInfo;
    std::string additional_report_info = "";

    void print() const {
        
        callInstInfo.print(report_class);

        if (additional_report_info != "") {
            errs() << ", ";
            errs() << additional_report_info;
        }
    }

};

struct UseGadget {
    std::string report_class = "undefined";
    CallInstInfo callInstInfo;
    StoreInstInfo storeInstInfo;
    std::string additional_report_info;

    void print() const {

        if (report_class == REPORT_CLASS_FPTR_COPY) {
            storeInstInfo.print(report_class);
        } 
        
        if (report_class == REPORT_CLASS_FPTR_CALL) {
            callInstInfo.print(report_class);
        }
    }
};

struct CriticalRegionInfo {
    CallInstInfo lock_sync;
    CallInstInfo unlock_sync;
    std::string target_func_ret_type;
    std::string target_func;
    std::vector<FreeGadget> free_gadgets;
    std::vector<UseGadget> use_gadgets;

    void print() const {
        
        
        errs() << llvm::formatv("\"target_func_ret_type\": \"{0}\", \"target_func\": \"{1}\"\n",
                    target_func_ret_type,
                    target_func);
        
        errs() << BLUE_START;
        errs() << "[LOCK-INFO]: ";lock_sync.print("lock"); errs() << "\n";
        errs() << "[UNLOCK-INFO]: ";unlock_sync.print("unlock"); errs() << "\n";
        errs() << COLOR_END;

        
        errs() << RED_START;
        unsigned freeCount = 1;
        for (auto &free_gadget: free_gadgets) {
            errs() << llvm::formatv("[FREE-INFO #{0}]: ", freeCount++);
            free_gadget.print();
            errs() << "\n";
        }
        
        unsigned useCount = 1;
        for (auto &use_gadget: use_gadgets) {
            errs() << llvm::formatv("[USE-INFO #{0}]: ", useCount++);
            use_gadget.print();
            errs() << "\n";
        }
        errs() << COLOR_END;

        errs() << "**************************************************************************************\n";
    }    
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_SYNCPRIMITIVES_H