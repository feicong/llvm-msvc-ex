#include "IndirectGlobalVars.h"

#include "CryptoUtils.h"
#include "Utils.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"


#include <cstdint>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#include <vector>

// #define RUN_BLOCK 1
// #define JMP_BORING 2
// #define JMP_SELECT 3

using namespace llvm;

static cl::opt<bool>
    RunIngvObfuscationPass("ind-gv", cl::init(false),
                           cl::desc("OLLVM - IngvObfuscationPass"));

PreservedAnalyses IngvObfuscationPass::run(Module &M,
                                           ModuleAnalysisManager &AM) {

  IndirectGlobalVariable gv;
  if (RunIngvObfuscationPass == true) {
    for (Function &Fn : M) {
      if (!toObfuscate(RunIngvObfuscationPass, &Fn, "ind-gv")) {
        continue;
      }
      gv.runOnFunction(Fn);
    }
    return PreservedAnalyses::none();
  }
  return PreservedAnalyses::all();
}

void IndirectGlobalVariable::NumberGlobalVariable(Function &F) {
  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    for (User::op_iterator op = (*I).op_begin(); op != (*I).op_end(); ++op) {
      Value *val = *op;
      if (auto GV = dyn_cast<GlobalVariable>(val)) {
        if (!GV->isThreadLocal() && GVNumbering.count(GV) == 0 &&
            !GV->isDLLImportDependent()) {
          GVNumbering[GV] = GlobalVariables.size();
          GlobalVariables.push_back(static_cast<GlobalVariable *>(val));
        }
      }
    }
  }
}

GlobalVariable *
IndirectGlobalVariable::get_indirect_global_variables(Function &F,
                                                      ConstantInt *EncKey) {
  const std::string GVName(F.getName().str() + "_IndirectGVars");
  GlobalVariable *GV = F.getParent()->getNamedGlobal(GVName);
  if (GV)
    return GV;

  std::vector<Constant *> Elements;
  for (const auto g_var : GlobalVariables) {
    Constant *ce =
        ConstantExpr::getBitCast(g_var, PointerType::getUnqual(F.getContext()));
    ce = ConstantExpr::getGetElementPtr(Type::getInt8Ty(F.getContext()), ce,
                                        EncKey);
    Elements.push_back(ce);
  }

  ArrayType *a_ty =
      ArrayType::get(PointerType::getUnqual(F.getContext()), Elements.size());
  Constant *CA = ConstantArray::get(a_ty, ArrayRef<Constant *>(Elements));
  GV =
      new GlobalVariable(*F.getParent(), a_ty, false,
                         GlobalValue::LinkageTypes::PrivateLinkage, CA, GVName);
  appendToCompilerUsed(*F.getParent(), {GV});
  return GV;
}

bool IndirectGlobalVariable::runOnFunction(Function &F) {
  NumberGlobalVariable(F);
  if (GlobalVariables.empty())
    return false;

  LLVMContext &Ctx = F.getContext();

  const uint64_t v = cryptoutils->get_uint64_t();
  IntegerType *intType = Type::getInt32Ty(Ctx);
  unsigned pointerSize =
      F.getEntryBlock().getModule()->getDataLayout().getTypeAllocSize(
          PointerType::getUnqual(F.getContext())); // Soule
  if (pointerSize == 8) {
    intType = Type::getInt64Ty(Ctx);
  }

  ConstantInt *EncKey = ConstantInt::get(intType, v, false);
  ConstantInt *EncKey1 = ConstantInt::get(intType, -v, false);

  Value *MySecret = ConstantInt::get(intType, 0, true);

  ConstantInt *Zero = ConstantInt::get(intType, 0);
  GlobalVariable *GVars = get_indirect_global_variables(F, EncKey1);

  for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    Instruction *Inst = &*I;
    if (isa<LandingPadInst>(Inst) || isa<CleanupPadInst>(Inst) ||
        isa<CatchPadInst>(Inst) || isa<CatchReturnInst>(Inst) ||
        isa<CatchSwitchInst>(Inst) || isa<ResumeInst>(Inst) ||
        isa<CallInst>(Inst)) {
      continue;
    }
    if (PHINode *PHI = dyn_cast<PHINode>(Inst)) {
      for (unsigned int i = 0; i < PHI->getNumIncomingValues(); ++i) {
        Value *val = PHI->getIncomingValue(i);
        if (GlobalVariable *GV = dyn_cast<GlobalVariable>(val)) {
          if (GVNumbering.count(GV) == 0) {
            continue;
          }

          Instruction *IP = PHI->getIncomingBlock(i)->getTerminator();
          IRBuilder<> IRB(IP);

          Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);
          Value *GEP = IRB.CreateGEP(GVars->getValueType(), GVars, {Zero, Idx});
          LoadInst *EncGVAddr =
              IRB.CreateLoad(GEP->getType(), GEP, GV->getName());

          Value *Secret = IRB.CreateAdd(EncKey, MySecret);
          Value *GVAddr =
              IRB.CreateGEP(Type::getInt8Ty(Ctx), EncGVAddr, Secret);
          GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
          GVAddr->setName("IndGV0_");
          PHI->setIncomingValue(i, GVAddr);
        }
      }
    } else {
      for (User::op_iterator op = Inst->op_begin(); op != Inst->op_end();
           ++op) {
        if (GlobalVariable *GV = dyn_cast<GlobalVariable>(*op)) {
          if (GVNumbering.count(GV) == 0) {
            continue;
          }

          IRBuilder<> IRB(Inst);
          Value *Idx = ConstantInt::get(intType, GVNumbering[GV]);
          Value *GEP = IRB.CreateGEP(GVars->getValueType(), GVars, {Zero, Idx});
          LoadInst *EncGVAddr =
              IRB.CreateLoad(GEP->getType(), GEP, GV->getName());

          Value *Secret = IRB.CreateAdd(EncKey, MySecret);
          Value *GVAddr =
              IRB.CreateGEP(Type::getInt8Ty(Ctx), EncGVAddr, Secret);
          GVAddr = IRB.CreateBitCast(GVAddr, GV->getType());
          GVAddr->setName("IndGV1_");
          Inst->replaceUsesOfWith(GV, GVAddr);
        }
      }
    }
  }
  return true;
}
