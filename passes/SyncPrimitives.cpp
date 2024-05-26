//===-- SyncPrimitives.cpp - Simple Sync Primitives Analysis ----*- C++ -*-===//
//
// Part of the VUsec Bsc. project on SCUAF.
// See SCUAF paper for reference (https://www.vusec.net/projects/ghostrace/).
// Author: Razvan Wist
// Supervisor: Cristiano Giuffrida
//
//===----------------------------------------------------------------------===//

#include "SyncPrimitives.h"

using namespace llvm;

//===-- Collection of critical regions, composed of a lock, unlock --------===//
//                      and use/free gadgets.

std::vector<CriticalRegionInfo> criticalRegions;

//===-- Collection supported function calls found -------------------------===//

std::unordered_map<Op, std::vector<CallInstInfo>> callInstructions;

std::unordered_map<Op, std::vector<StoreInstInfo>> storeInstructions;

//===-- Function calls supported, along with type -------------------------===//

std::unordered_map<std::string, Op> callInstbyType = {
    {"free", Op::FREE},
    {"list_del", Op::LISTDEL}
};

//===-- Function - check for dominance between calls ----------------------===//
//
// This function examines whether the first call dominates the second call
// within the program. 

bool dominates(Instruction *firstCall, Instruction *secondCall, Module &M, ModuleAnalysisManager &MAM) {
    if (!firstCall || !secondCall || firstCall == secondCall) {
        return false;
    }

    auto *firstBB = firstCall->getParent();
    auto *secondBB = secondCall->getParent();

    if (!firstBB || !secondBB) {
        return false;
    }

    auto *firstFunc = firstBB->getParent();
    auto *secondFunc = secondBB->getParent();

    if (!firstFunc || !secondFunc || firstFunc != secondFunc) {
        return false;
    }

    auto &DT = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager().getResult<DominatorTreeAnalysis>(*firstFunc);

    if (firstBB == secondBB) {
        return DT.dominates(firstCall, secondCall);
    }

    auto *terminator = firstBB->getTerminator();

    if (terminator) {
        if (llvm::BranchInst *BI = llvm::dyn_cast<llvm::BranchInst>(terminator)) {
            for (unsigned i = 0; i < BI->getNumSuccessors(); i++) {
                if (BI->getSuccessor(i) && DT.dominates(BI->getSuccessor(i), secondBB)) {
                    return true;
                }
            }
        }
    }
    
    return DT.dominates(firstBB, secondBB);
}

bool postdominates(Instruction *firstCall, Instruction *secondCall, Module &M, ModuleAnalysisManager &MAM) {
    if (!firstCall || !secondCall || firstCall == secondCall) {
        return false;
    }

    auto *firstBB = firstCall->getParent();
    auto *secondBB = secondCall->getParent();

    if (!firstBB || !secondBB) {
        return false;
    }

    auto *firstFunc = firstBB->getParent();
    auto *secondFunc = secondBB->getParent();

    if (!firstFunc || !secondFunc || firstFunc != secondFunc) {
        return false;
    }

    auto &PDT = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager().getResult<PostDominatorTreeAnalysis>(*firstFunc);

    if (firstBB == secondBB) {
        return PDT.dominates(firstCall, secondCall);
    }

    return PDT.dominates(firstBB, secondBB);
}

//===-- Function - solve type name ----------------------------------------===//
//
// This function retrieves the name of a given LLVM type. 

// It covers a variety of types including primitive types, arrays, functions,
// pointers, structs, floating point types, and vectors. It uses MDString to 
// store the newly created string in order to avoid memory leaks.
static StringRef solveTypeName(Type *Ty) {
    if (Ty->isVoidTy()) {
        return VOID_TYPE_STRING;
    }

    if (Ty->isArrayTy()) {
        llvm::ArrayType *AT = dyn_cast<ArrayType>(Ty);
        SmallString<64> Buffer;
        raw_svector_ostream OS(Buffer);
        OS << ARRAY_TYPE_STRING << "_" <<solveTypeName(AT->getElementType()).str() << "[" << AT->getNumElements() << "]";
        auto *MDName = MDString::get(Ty->getContext(), OS.str());
        return MDName->getString();
    }

    if (Ty->isFunctionTy()) {
        llvm::FunctionType *FT = dyn_cast<FunctionType>(Ty);
        SmallString<128> Buffer;
        raw_svector_ostream OS(Buffer);
        OS << FUNCTION_TYPE_STRING << "_with_ret_type_" << solveTypeName(FT->getReturnType()).str();

        OS << "(";
        for (unsigned i = 0; i < FT->getNumParams(); i++) {
            if (i > 0) {
                OS << ", ";
            }

            OS << solveTypeName(FT->getParamType(i)).str();
        }
        OS << ")";

        auto *MDName = MDString::get(Ty->getContext(), OS.str());
        return MDName->getString();
    }

    if (Ty->isIntegerTy()) {
        SmallString<64> Buffer;
        raw_svector_ostream OS(Buffer);
        OS << INT_TYPE_STRING << "_" << dyn_cast<IntegerType>(Ty)->getBitWidth();
        auto *MDName = MDString::get(Ty->getContext(), OS.str());
        return MDName->getString();
    }

    if (Ty->isPointerTy()) {
        return PTR_TYPE_STRING;
    }

    if (Ty->isStructTy()) {
        if (!dyn_cast<StructType>(Ty)->hasName())
        return LITERAL_STRUCT_TYPE_STRING;

        auto Name = Ty->getStructName();

        SmallString<64> Buffer(Name);
        for (auto &Iter : Buffer)
        if (Iter == '.' || Iter == ':')
            Iter = '_';
        auto *MDName = MDString::get(Ty->getContext(), Buffer.str());
        return MDName->getString();
    }

    if (Ty->isFloatingPointTy()) {
        if (Ty->isFloatTy()) return FLOAT_TYPE_STRING;
        if (Ty->isDoubleTy()) return DOUBLE_TYPE_STRING;
        
        return FLOATING_TYPE_STRING;
    }

    if (Ty->isVectorTy()) {
        VectorType *VT = dyn_cast<VectorType>(Ty);
        SmallString<64> Buffer;
        raw_svector_ostream OS(Buffer);
        OS << VECTOR_TYPE_STRING << "<" << solveTypeName(VT->getElementType()).str() << " x " << VT->getElementCount() << ">";
        auto *MDName = MDString::get(Ty->getContext(), OS.str());
        return MDName->getString();
    }

    return UNKNOWN_TYPE_STRING;
}

//===-- Function - determine operand scope --------------------------------===//
//
// This function retrieves the scope information of a given LLVM value. 

// It determines the scope based on whether the value is an instruction or
// a global variable, considering the parent basic block, function, and module.
std::string getOperandScope(Value* operandValue) {

    if (auto *LI = dyn_cast<llvm::LoadInst>(operandValue)) {
        return getOperandScope(LI->getPointerOperand());
    }

    llvm::BasicBlock *operandBB = nullptr;
    llvm::Function *operandFunction = nullptr;
    llvm::Module *operandModule = nullptr;

    if (auto *inst = dyn_cast<llvm::Instruction>(operandValue)) {
        operandBB = inst->getParent();
        operandFunction = inst->getFunction();
        operandModule = inst->getModule();
 
        // Build the scope string with safe checks for null pointers and names.
        return "$" + (operandBB && operandBB->hasName() ? operandBB->getName().str() : "unnamed") +
               "$" + (operandFunction && operandFunction->hasName() ? operandFunction->getName().str() : "unnamed") +
               "$" + (operandModule ? operandModule->getSourceFileName() : "unnamed");
    } else if (auto *globalVariable = dyn_cast<llvm::GlobalVariable>(operandValue)) {
        operandModule = globalVariable->getParent();
        return "$GLOBAL$" + (operandModule ? operandModule->getSourceFileName() : "unnamed");
    }

    return "$UNDEFINED_VARIABLE"; 
}

std::string getDebugInfo(llvm::Instruction *inst) {
    

    if (!inst) {
        return "(debug-error)";
    }

    std::string call_path_string = "";
    auto debugLoc = inst->getDebugLoc();

    if (debugLoc) {

        if (debugLoc.getInlinedAt()) {

            if (!debugLoc) {
                call_path_string = "(no-debug-info)";
            }

            while (debugLoc) {
                if (debugLoc->getScope()) {

                    if (debugLoc->getLine()) {
                        call_path_string = " +" + std::to_string(debugLoc->getLine()) + call_path_string;
                    } else {
                        call_path_string = "(no-debug-line)" + call_path_string;
                    }

                    if (!debugLoc->getScope()->getFilename().empty()) {
                        call_path_string = debugLoc->getScope()->getFilename().str() + call_path_string;
                    }
                    if (!debugLoc->getScope()->getName().empty()) {
                        call_path_string = "@" + debugLoc->getScope()->getName().str() + "():" + call_path_string;
                    } else if (inst->getFunction() && inst->getFunction()->hasName()) {
                        call_path_string = "@" + inst->getFunction()->getName().str() + "():" + call_path_string;
                    } else {
                        call_path_string = "@undef_func():" + call_path_string;
                    }
                } else {
                    call_path_string = "(no-debug-scope):" + call_path_string;
                }

                if (debugLoc.getInlinedAt()) {
                    call_path_string = " -> " + call_path_string;
                }

                debugLoc = debugLoc.getInlinedAt();
            }
        } else {
            if (debugLoc->getScope()) {
                if (!debugLoc->getScope()->getName().empty()) {
                    call_path_string += "@" + debugLoc->getScope()->getName().str() + "():";
                } else if (inst->getFunction() && inst->getFunction()->hasName()) {
                    call_path_string += "@" + inst->getFunction()->getName().str() + "():";
                } else {
                    call_path_string += "@undef_func():";
                }

                if (!debugLoc->getScope()->getFilename().empty()) {
                    call_path_string += debugLoc->getScope()->getFilename().str();
                } else {
                    call_path_string += "no-debug-directory";
                }

                if (debugLoc->getLine()) {
                    call_path_string += " +" + std::to_string(debugLoc->getLine());
                } else {
                    call_path_string += "(no-debug-line)";
                }
            } else {
                call_path_string = "(no-debug-scope):";
            }
        }
    } else {
        call_path_string = "(no-debug-info)";
    }

    return call_path_string;
}

std::string getCallPathString(std::vector<CallInst*> call_path) {
    std::string call_path_string = "";

    if (!call_path.empty() && call_path.back()) {

        if (call_path.back()->getDebugLoc() && call_path.back()->getDebugLoc().getInlinedAt()) {
            call_path_string = getDebugInfo(call_path.back());
        } else {
            for (const auto& call_inst : call_path) {
                if (call_path_string != "") {
                    call_path_string += " -> ";
                }
                
                call_path_string += getDebugInfo(call_inst);
            }
        }
    }

    return call_path_string;
}

//===-- Function - determine operand types --------------------------------===//
//
// This function retrieves the types of operands associated with a given LLVM 
// value. 

// It iterates through the value and determines the types based on its 
// characteristics, such as being an alloca instruction, a global variable,
// a getelementptr instruction,or a load instruction.
std::vector<std::string> getOperandTypes(Value* operandValue) {
    std::vector<std::string> operandTypes;
    
    if (!operandValue) return operandTypes;

    while (operandValue) {
        std::string varName = "";
        Type* operandType = nullptr;

        // Determine the type of the operandValue
        if (auto *allocaInst = dyn_cast<AllocaInst>(operandValue)) {
            if (allocaInst->hasName()) {
                varName = allocaInst->getName().str();
            }
            operandType = allocaInst->getAllocatedType();
            operandValue = nullptr;
            
        } else if (auto *globalVar = dyn_cast<GlobalVariable>(operandValue)) {
            if (globalVar->hasName()) {
                varName = globalVar->getName().str();
            }
            operandType = globalVar->getValueType();       
            operandValue = nullptr;
        } else if (auto *GEP = dyn_cast<GetElementPtrInst>(operandValue)) {
            operandType = GEP->getResultElementType();
            operandValue = GEP->getPointerOperand();
        } else if (auto *loadInst = dyn_cast<LoadInst>(operandValue)) {
            operandType = nullptr;
            operandValue = loadInst->getPointerOperand();
        } else {
            if (operandValue->hasName()) {
                varName = operandValue->getName().str();
            }
            operandType = operandValue->getType();
            operandValue = nullptr;
        }

        if (operandType) {
            operandTypes.push_back(solveTypeName(operandType).str());

            if (varName != "") {
                operandTypes.back() += "<" + varName + ">";
            }
        }
    }

    std::reverse(operandTypes.begin(), operandTypes.end());
    return operandTypes;
}


void handleDirectCallInst(CallInst* callInst, std::vector<CallInst*>call_path) {
    if (callInst && callInst->getCalledFunction() && callInst->getCalledFunction()->hasName()) {
        llvm::StringRef calledFunctionName = callInst->getCalledFunction()->getName();
        bool isSupported = callInstbyType.find(calledFunctionName.str()) != callInstbyType.end();

        CallInstInfo info;
        
        info.call_inst_type = isSupported ? callInstbyType[calledFunctionName.str()] : Op::UNKNOWN;

        if (calledFunctionName.contains("mutex_lock")) {
            info.call_inst_type = Op::LOCK;
        }

        if (calledFunctionName.contains("mutex_unlock")) {
            info.call_inst_type = Op::UNLOCK;
        }

        if (callInst->getCalledFunction()->arg_size() > 0) {
            auto *calledFunctionFirstArg = callInst->getCalledFunction()->arg_begin();
            info.operand_scope = getOperandScope(callInst->getArgOperand(0));
            info.operand_type_list = getOperandTypes(calledFunctionFirstArg);
        }
        
        info.call_path = call_path;
        info.call_path_string = getCallPathString(call_path);
        callInstructions[info.call_inst_type].emplace_back(info);
    }
}

void handleInirectCallInst(CallInst* callInst, std::vector<CallInst*>call_path) {
    if (callInst && callInst->getCalledOperand()) {
        CallInstInfo info;

        if (auto *calledOperand = dyn_cast<LoadInst>(callInst->getCalledOperand())) {
            if (calledOperand->getPointerOperand()) {
                if (calledOperand->getPointerOperand()->getType()->isPointerTy()) {
                    info.call_inst_type = Op::FPTR_CALL;
                    info.call_path = call_path;
                    info.call_path_string = getCallPathString(call_path);
                    info.operand_scope = getOperandScope(calledOperand->getPointerOperand());
                    info.operand_type_list = getOperandTypes(calledOperand->getPointerOperand());
                    callInstructions[info.call_inst_type].emplace_back(info);
                }
            }
        }
    }
}

void handleInst(Instruction* inst, std::vector<CallInst*>call_path = {}) {

    // Early exit for null pointers or unresolved indirect calls
    if (!inst) {
        return;
    }

    if (auto *CI = dyn_cast<CallInst>(inst)) {
        call_path.emplace_back(CI);

        if (CI->isIndirectCall()) {
            handleInirectCallInst(CI, call_path);
        } else {
            handleDirectCallInst(CI, call_path);
        }

        if (CI->getCalledFunction()){
            for (auto &BB : *CI->getCalledFunction()) {
                for (auto &I : BB) {
                    handleInst(&I, call_path);
                }
            }
        }
    } else if (auto *SI = dyn_cast<StoreInst>(inst)) {
        StoreInstInfo storeInstInfo;
        storeInstInfo.store_inst = SI;
        storeInstInfo.operand_scope = getOperandScope(SI->getPointerOperand());
        storeInstInfo.operand_type_list = getOperandTypes(SI->getPointerOperand());
        storeInstInfo.call_path = call_path;
        storeInstInfo.call_path_string = (getCallPathString(call_path) != "") ? getCallPathString(call_path) : getDebugInfo(inst);
        if (isa<ConstantPointerNull>(SI->getValueOperand())) {
            storeInstInfo.store_inst_type = Op::UPDATE_NULL;
        } else if (isa<Function>(SI->getValueOperand())) {
            storeInstInfo.store_inst_type = Op::FPTR_COPY;
        } else {
            storeInstInfo.store_inst_type = Op::UPDATE_VAL;
        }

        storeInstructions[storeInstInfo.store_inst_type].emplace_back(storeInstInfo);
    }
}

void buildCriticalRegions(Module &M, ModuleAnalysisManager &MAM) {
    
    while(!callInstructions[Op::LOCK].empty() && !callInstructions[Op::UNLOCK].empty()) {
        std::unordered_map<Op, std::vector<CallInstInfo>> reportedCallInstructions;
        std::unordered_map<Op, std::vector<StoreInstInfo>> reportedStoreInstructions;

        for (const auto& lock_sync : callInstructions[Op::LOCK]) {
            bool dominates_other_locks = false;
            for (const auto& other_lock_sync : callInstructions[Op::LOCK]) {
                for (const auto& lock_call_path_inst : lock_sync.call_path) {
                    for (const auto& other_lock_call_path_inst : other_lock_sync.call_path) {
                        if (dominates(lock_call_path_inst, other_lock_call_path_inst, M, MAM) || postdominates(other_lock_call_path_inst, lock_call_path_inst, M, MAM)) {
                            dominates_other_locks = true;
                        }
                    }
                }
            }

            if (!dominates_other_locks) {
                reportedCallInstructions[Op::LOCK].emplace_back(lock_sync);
            }
        }

        for (const auto &lock_sync : reportedCallInstructions[Op::LOCK]) {
            std::vector<CallInstInfo> matching_unlocks;

            for (const auto& unlock_sync : callInstructions[Op::UNLOCK]) {
                for (const auto& lock_call_path_inst : lock_sync.call_path) {
                    for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                        if (lock_sync.operand_type_list == unlock_sync.operand_type_list && lock_sync.operand_scope == unlock_sync.operand_scope &&
                                (dominates(lock_call_path_inst, unlock_call_path_inst, M, MAM) || 
                                postdominates(unlock_call_path_inst, lock_call_path_inst, M, MAM))) {
                            matching_unlocks.emplace_back(unlock_sync);
                        } 
                    }
                }
            }

            std::vector<CallInstInfo> most_dominating_unlocks;

            for (const auto& unlock_sync : matching_unlocks) {
                bool is_dominated_by_matching_unlock = false;

                for (const auto& other_unlock_sync : matching_unlocks) {
                    for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                        for (const auto& other_unlock_call_path_inst : other_unlock_sync.call_path) {
                            if (dominates(other_unlock_call_path_inst, unlock_call_path_inst, M, MAM) || 
                                postdominates(unlock_call_path_inst, other_unlock_call_path_inst, M, MAM)) {
                                    is_dominated_by_matching_unlock = true;
                                }
                        }
                    }
                }

                if (!is_dominated_by_matching_unlock) {
                    reportedCallInstructions[Op::UNLOCK].emplace_back(unlock_sync);
                    most_dominating_unlocks.emplace_back(unlock_sync);
                }
            }

            for (const auto& unlock_sync : most_dominating_unlocks) {
                for (const auto& lock_call_path_inst : lock_sync.call_path) {
                    for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                        if (dominates(lock_call_path_inst, unlock_call_path_inst, M, MAM) || postdominates(unlock_call_path_inst, lock_call_path_inst, M, MAM)) {
                            CriticalRegionInfo criticalRegion;

                            criticalRegion.lock_sync = lock_sync;
                            criticalRegion.unlock_sync = unlock_sync;
                            criticalRegion.target_func_ret_type = solveTypeName(lock_call_path_inst->getFunction()->getReturnType()).str();
                            criticalRegion.target_func = lock_call_path_inst->getFunction()->getName().str();

                            for (const auto& free : callInstructions[Op::FREE]) {
                                for (const auto& free_call_path_inst : free.call_path) {
                                    if (dominates(lock_call_path_inst, free_call_path_inst, M, MAM) &&
                                        dominates(free_call_path_inst, unlock_call_path_inst, M, MAM)) {

                                        // REPORT GUARDED_FREE(ptr)
                                        FreeGadget freeGadget;
                                        freeGadget.callInstInfo = free;
                                        freeGadget.report_class = REPORT_CLASS_GUARDED_FREE;
                                        criticalRegion.free_gadgets.emplace_back(freeGadget);
                                        reportedCallInstructions[Op::FREE].emplace_back(free);

                                        // REPORT GUARDED_FREE(ptr) + ptr NULL assign
                                        for (const auto& update : storeInstructions[Op::UPDATE_NULL] ) {
                                            for (const auto& free_call_path_inst : free.call_path) {
                                                if (update.operand_type_list == free.operand_type_list && update.operand_scope == free.operand_scope) {
                                                    bool isDominatedByFree = false;
                                                    if (dominates(free_call_path_inst, update.store_inst, M, MAM)) {
                                                        isDominatedByFree = true;
                                                    } else {
                                                        for (const auto& update_call_path_inst : update.call_path) {
                                                            if (dominates(free_call_path_inst, update_call_path_inst, M, MAM)) {
                                                                isDominatedByFree = true;
                                                            }
                                                        }
                                                    }

                                                    if (isDominatedByFree) {
                                                        for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                                                            bool dominatesUnlock = false;
                                                            if (dominates(update.store_inst, unlock_call_path_inst, M, MAM)) {
                                                                dominatesUnlock = true;
                                                            } else {
                                                                for (const auto& update_call_path_inst : update.call_path) {
                                                                    if (dominates(update_call_path_inst, unlock_call_path_inst, M, MAM)) {
                                                                        dominatesUnlock = true;
                                                                    }
                                                                }
                                                            }

                                                            if (dominatesUnlock) {
                                                                FreeGadget freeGadget;
                                                                freeGadget.report_class = REPORT_CLASS_GUARDED_FREE_NULL; 
                                                                std::string update_position = getDebugInfo(update.store_inst);
                                                                freeGadget.additional_report_info = "";
                                                                freeGadget.callInstInfo = free;
                                                                criticalRegion.free_gadgets.emplace_back(freeGadget);
                                                                reportedStoreInstructions[Op::UPDATE_NULL].emplace_back(update);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }

                                        // REPORT GUARDED_FREE(ptr) + ptr VAL assign
                                        for (const auto& update : storeInstructions[Op::UPDATE_VAL] ) {
                                            for (const auto& free_call_path_inst : free.call_path) {
                                                if (update.operand_type_list == free.operand_type_list && update.operand_scope == free.operand_scope) {
                                                    bool isDominatedByFree = false;
                                                    if (dominates(free_call_path_inst, update.store_inst, M, MAM)) {
                                                        isDominatedByFree = true;
                                                    } else {
                                                        for (const auto& update_call_path_inst : update.call_path) {
                                                            if (dominates(free_call_path_inst, update_call_path_inst, M, MAM)) {
                                                                isDominatedByFree = true;
                                                            }
                                                        }
                                                    }

                                                    if (isDominatedByFree) {
                                                        for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                                                            bool dominatesUnlock = false;
                                                            if (dominates(update.store_inst, unlock_call_path_inst, M, MAM)) {
                                                                dominatesUnlock = true;
                                                            } else {
                                                                for (const auto& update_call_path_inst : update.call_path) {
                                                                    if (dominates(update_call_path_inst, unlock_call_path_inst, M, MAM)) {
                                                                        dominatesUnlock = true;
                                                                    }
                                                                }
                                                            }

                                                            if (dominatesUnlock) {
                                                                FreeGadget freeGadget;
                                                                freeGadget.report_class = REPORT_CLASS_GUARDED_FREE_VAL;
                                                                std::string update_position = getDebugInfo(update.store_inst);
                                                                freeGadget.additional_report_info = "";
                                                                freeGadget.callInstInfo = free;
                                                                criticalRegion.free_gadgets.emplace_back(freeGadget);
                                                                reportedStoreInstructions[Op::UPDATE_VAL].emplace_back(update);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }

                                        // REPORT GUARDED_FREE(ptr) + list_del()
                                        for (const auto& update : callInstructions[Op::LISTDEL] ) {
                                            for (const auto& free_call_path_inst : free.call_path) {
                                                if (update.operand_type_list == free.operand_type_list && update.operand_scope == free.operand_scope) {
                                                    bool isDominatedByFree = false;
                                                    
                                                    for (const auto& update_call_path_inst : update.call_path) {
                                                        if (dominates(free_call_path_inst, update_call_path_inst, M, MAM)) {
                                                            isDominatedByFree = true;
                                                        }
                                                    }

                                                    if (isDominatedByFree) {
                                                        for (const auto& unlock_call_path_inst : unlock_sync.call_path) {
                                                            bool dominatesUnlock = false;
                                                            
                                                            for (const auto& update_call_path_inst : update.call_path) {
                                                                if (dominates(update_call_path_inst, unlock_call_path_inst, M, MAM)) {
                                                                    dominatesUnlock = true;
                                                                }
                                                            }

                                                            if (dominatesUnlock) {
                                                                FreeGadget freeGadget;
                                                                freeGadget.report_class = REPORT_CALSS_GUARDED_FREE_LIST_DEL; 
                                                                std::string update_position = getDebugInfo(update.call_path.back());
                                                                freeGadget.additional_report_info = "";
                                                                freeGadget.callInstInfo = free;
                                                                criticalRegion.free_gadgets.emplace_back(freeGadget);
                                                                reportedCallInstructions[Op::LISTDEL].emplace_back(update);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }

                            // REPORT GUARDED FPTR COPY
                            for (const auto& use : storeInstructions[Op::FPTR_COPY]) {
                                bool dominatesUnlock = false;

                                if (dominates(use.store_inst, unlock_call_path_inst, M, MAM)) {
                                    dominatesUnlock = true;
                                } else {
                                    for (const auto& use_call_path_inst : use.call_path) {
                                        if (dominates(lock_call_path_inst, use_call_path_inst, M, MAM) &&
                                            dominates(use_call_path_inst, unlock_call_path_inst, M, MAM)) {
                                            dominatesUnlock = true;
                                        }
                                    }
                                }

                                if (dominatesUnlock) {
                                    UseGadget useGadget;
                                    useGadget.report_class = REPORT_CLASS_FPTR_COPY;
                                    std::string update_position = getDebugInfo(use.store_inst);
                                    useGadget.additional_report_info = "";
                                    useGadget.storeInstInfo = use;
                                    criticalRegion.use_gadgets.emplace_back(useGadget);   
                                    reportedStoreInstructions[Op::FPTR_COPY].emplace_back(use);
                                }
                            }

                            // REPORT GUARDED FPTR CALL
                            for (const auto& use : callInstructions[Op::FPTR_CALL]) {
                                bool dominatesUnlock = false;

                                for (const auto& use_call_path_inst : use.call_path) {
                                    if (dominates(lock_call_path_inst, use_call_path_inst, M, MAM) &&
                                        dominates(use_call_path_inst, unlock_call_path_inst, M, MAM)) {
                                        dominatesUnlock = true;
                                    }
                                }

                                if (dominatesUnlock) {
                                    UseGadget useGadget;
                                    useGadget.report_class = REPORT_CLASS_FPTR_CALL;
                                    std::string update_position = getDebugInfo(use.call_path.back());
                                    useGadget.additional_report_info = "";
                                    useGadget.callInstInfo = use;
                                    criticalRegion.use_gadgets.emplace_back(useGadget);
                                    reportedCallInstructions[Op::FPTR_CALL].emplace_back(use);
                                }
                            }

                            criticalRegions.emplace_back(criticalRegion);
                        }
                    }
                }
            }
        }

        if (reportedCallInstructions[Op::LOCK].empty() || reportedCallInstructions[Op::UNLOCK].empty()) {
            break;
        } else {
            for (const auto& pair : reportedCallInstructions) {
                if (callInstructions.find(pair.first) != callInstructions.end()) {
                    auto &diff = callInstructions[pair.first];

                    for (const auto &call : pair.second) {
                        auto it = std::remove(diff.begin(), diff.end(), call);
                        diff.erase(it, diff.end());
                    }
                }
            }

            for (const auto& pair : reportedStoreInstructions) {
                if (storeInstructions.find(pair.first) != storeInstructions.end()) {
                    auto &diff = storeInstructions[pair.first];

                    for (const auto &call : pair.second) {
                        auto it = std::remove(diff.begin(), diff.end(), call);
                        diff.erase(it, diff.end());
                    }
                }
            }
        }
    }
}

void printCriticalRegionsInfo() {
    int regionIndex = 1;
    for (const auto& criticalRegion : criticalRegions) {
        errs() << llvm::formatv("Critical Region #{0} ", regionIndex++);
        criticalRegion.print();
    }
}

PreservedAnalyses SyncPrimitivesPass::run(Module &M, ModuleAnalysisManager &MAM) {
    errs() << "[BUILDING] Critical Regions...\n";
    
    for (Function &F : M) {
        for (BasicBlock &BB : F) {
            for (Instruction &I : BB) {
                handleInst(&I);
            }
        }
        
        buildCriticalRegions(M, MAM);
    }

    printCriticalRegionsInfo();
    errs() << "[!] Build completed!\n";

    return PreservedAnalyses::all();
}

/* New PM Registration */
llvm::PassPluginLibraryInfo getSyncPrimitivesPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "SyncPrimitives", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, llvm::ModulePassManager &MPM,
                   ArrayRef<llvm::PassBuilder::PipelineElement> InnerPipeline) {
                  if (Name == "sync-primitives") {
                    MPM.addPass(SyncPrimitivesPass());
                    return true;
                  }
                  return false;
                });

             // Register the pass for LTO (Full Link Time Optimization)
            PB.registerOptimizerLastEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                  MPM.addPass(SyncPrimitivesPass());
                });

            // Register the pass for ThinLTO (Thin Link Time Optimization)
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                  MPM.addPass(SyncPrimitivesPass());
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return getSyncPrimitivesPluginInfo();
}