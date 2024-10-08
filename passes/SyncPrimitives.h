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

#include "llvm/IR/PassManager.h" // new PassManager(PM)
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/PostDominators.h"

#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <queue>
#include <vector>
#include <string>
#include <algorithm> // Ensure to include for std::remove and std::erase

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
#define REPORT_CLASS_GUARDED_FREE_LIST_DEL "guarded_free_list_del"
#define REPORT_CLASS_FPTR_COPY "fptr_copy"
#define REPORT_CLASS_FPTR_CALL "fptr_call"

enum class Op { LOCK, UNLOCK, FREE, UPDATE_NULL, UPDATE_VAL, LISTDEL, FPTR_CALL, FPTR_COPY, UNKNOWN };

namespace llvm {

class SyncPrimitivesPass : public PassInfoMixin<SyncPrimitivesPass> {
public:
  PreservedAnalyses run(Module  &M, ModuleAnalysisManager &MAM);
};

struct StoreInstInfo {
    enum Op store_inst_type = Op::UNKNOWN;
    llvm::StoreInst* store_inst = nullptr;
    std::string operand_scope;
    std::vector<std::string> operand_type_list;
    std::vector<llvm::CallInst*> call_path;
    std::string call_path_string;
    unsigned nesting_level;

    void print(std::string report_class) const {
        if (store_inst) {
            errs() << llvm::formatv("report_class={0}", 
                    report_class);
            errs() << ", ";
            errs() << llvm::formatv("{0}_call_path={1}", 
                    report_class,
                    call_path_string);
            errs() << ", ";

            errs() << llvm::formatv("{0}_nesting_level={1}", 
                    report_class,
                    nesting_level);
            errs() << ", ";

            std::string typesStr = "";
            for (const auto& type : operand_type_list) {
                typesStr += " " + type;
            }
            errs() << llvm::formatv("{0}_operand_scope={1}, {0}_operand_type_list=[{2} ]",
                    report_class,
                    operand_scope,
                    typesStr);
            errs();
        }
    }    

    bool operator==(const StoreInstInfo& other) const {
        return call_path_string == other.call_path_string;
    }

    bool operator!=(const StoreInstInfo& other) const {
        return call_path_string != other.call_path_string;
    }
};

struct CallInstInfo {
    Op call_inst_type = Op::UNKNOWN;
    std::string operand_scope;
    std::vector<std::string> operand_type_list;
    std::vector<llvm::CallInst*> call_path;
    std::string call_path_string;
    unsigned nesting_level;
    
    void print(std::string report_class) const {
        errs() << llvm::formatv("report_class={0}", 
                    report_class);
        errs() << ", ";
        
        errs() << llvm::formatv("{0}_call_path={1}", 
                report_class,
                call_path_string);
        errs() << ", ";

        errs() << llvm::formatv("{0}_nesting_level={1}", 
                    report_class,
                    nesting_level);
        errs() << ", ";

        std::string typesStr = "";
        for (const auto& type : operand_type_list) {
            typesStr += " " + type;
        }
        errs() << llvm::formatv("{0}_operand_scope={1}, {0}_operand_type_list=[{2} ]",
                    report_class,
                    operand_scope,
                    typesStr);
        errs() << ", ";

        std::string func_name = "unnamed_function";

        if (!call_path.empty()) {
            if (call_path.back()->isIndirectCall()) {
                Value *calledValue = call_path.back()->getCalledOperand();
                if (calledValue->hasName()) {
                    func_name = calledValue->getName().str();
                } else {
                    func_name = "indirect function found (manual inspection is needed to find the name)";
                }
            } else {
                Function *calledFunction = call_path.back()->getCalledFunction();
                if (calledFunction->hasName()) {
                    func_name = calledFunction->getName().str();
                }
            }
        }

        errs() << llvm::formatv("{0}_func={1}", 
                    report_class,
                    func_name);
    }    

    bool operator==(const CallInstInfo& other) const {
        return call_path_string == other.call_path_string;
    }

    bool operator!=(const CallInstInfo& other) const {
        return call_path_string != other.call_path_string;
    }
};

struct FreeGadget {
    std::string report_class = "undefined";
    CallInstInfo callInstInfo;
    StoreInstInfo storeInstInfo;
    std::string additional_report_info = "";

    void print() const {
        callInstInfo.print(report_class);

        if (additional_report_info != "") {
            errs() << ", ";
            errs() << additional_report_info;
        }
    }

    bool operator==(const FreeGadget& other) const {
        return report_class == other.report_class && callInstInfo.call_path_string == other.callInstInfo.call_path_string;
    }

    bool operator!=(const FreeGadget& other) const {
        return report_class != other.report_class || callInstInfo.call_path_string != other.callInstInfo.call_path_string;
    }

};

struct UseGadget {
    std::string report_class = "undefined";
    CallInstInfo callInstInfo;
    StoreInstInfo storeInstInfo;
    std::string additional_report_info = "";

    void print() const {
        if (report_class == REPORT_CLASS_FPTR_COPY) {
            storeInstInfo.print(report_class);
        } 
        
        if (report_class == REPORT_CLASS_FPTR_CALL) {
            callInstInfo.print(report_class);
        }

        if (additional_report_info != "") {
            errs() << ", ";
            errs() << additional_report_info;
        }
    }

    bool operator==(const UseGadget& other) const {
        if (report_class == REPORT_CLASS_FPTR_COPY) {
            return report_class == other.report_class && storeInstInfo.call_path_string == other.storeInstInfo.call_path_string;
        } else if (REPORT_CLASS_FPTR_CALL) {
            return report_class == other.report_class && callInstInfo.call_path_string == other.callInstInfo.call_path_string;
        }
    }

    bool operator!=(const UseGadget& other) const {
        if (report_class == REPORT_CLASS_FPTR_COPY) {
            return !(report_class == other.report_class && storeInstInfo.call_path_string == other.storeInstInfo.call_path_string);
        } else if (REPORT_CLASS_FPTR_CALL) {
            return !(report_class == other.report_class && callInstInfo.call_path_string == other.callInstInfo.call_path_string);
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
        errs() << llvm::formatv("target_func_ret_type={0}, target_func={1}\n",
                    target_func_ret_type,
                    target_func);
        
        errs() << "[LOCK-INFO]: ";lock_sync.print("lock"); errs() << "\n";
        errs() << "[UNLOCK-INFO]: ";unlock_sync.print("unlock"); errs() << "\n";
        
        unsigned freeCount = 0;
        for (auto &free_gadget: free_gadgets) {
            errs() << llvm::formatv("[FREE-INFO #{0}]: ", ++freeCount);
            free_gadget.print();
            errs() << "\n";
        }
        
        unsigned useCount = 0;
        for (auto &use_gadget: use_gadgets) {
            errs() << llvm::formatv("[USE-INFO #{0}]: ", ++useCount);
            use_gadget.print();
            errs() << "\n";
        }

        errs() << "**************************************************************************************\n";
    }    
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_SYNCPRIMITIVES_H