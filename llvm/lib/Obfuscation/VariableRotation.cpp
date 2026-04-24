#include "VariableRotation.h"
#include "BogusControlFlow.h"
#include "ConstObfuscation.h"
#include "CryptoUtils.h"
#include "Flattening.h"
#include "IndirectGlobalVars.h"
#include "Utils.h"
#include "VMFlatten.h"

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
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/LowerSwitch.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <cstdint>
#include <cstring>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#ifdef _MSC_VER
#include <vcruntime_string.h>
#endif
#include <vector>

using namespace llvm;
static cl::opt<bool> RunVarRot("x-var-rot", cl::init(false),
                               cl::desc("OLLVM - variable rotation"));

namespace {
struct VariableRotation {
  Function *createRotateFunc(Module *m, PointerType *ptrType, Twine &name);
  void processFunction(Function &f, const SetVector<Function *> &shift);
  bool processVars(Function &f, SetVector<AllocaInst *> &vars,
                   Function *rotateFunc);
  bool isUsedByInst(Instruction *inst, const Value *var);
  bool runOnModule(Module &m);
};

Function *VariableRotation::createRotateFunc(Module *m, PointerType *ptrType,
                                             Twine &name) {

  IRBuilder<> builder(m->getContext());

  // Function argument types
  std::vector<Type *> funcArgs(
      {ptrType,
                                builder.getInt32Ty(), builder.getInt32Ty()});

  // Create the function type and function
  FunctionType *funcType =
      FunctionType::get(Type::getVoidTy(m->getContext()), funcArgs, false);
  Function *theFunction =
      Function::Create(funcType, Function::PrivateLinkage,
                                           name, m);

  // Define the function arguments
  Function::arg_iterator args = theFunction->arg_begin();
  Value *a1 = args++;
  a1->setName("a1");
  Value *a2 = args++;
  a2->setName("a2");
  Value *a3 = args++;
  a3->setName("a3");

  // Create the entry block and other blocks
  BasicBlock *entryBB =
      BasicBlock::Create(m->getContext(), "entry", theFunction);
  BasicBlock *outerLoopPreheaderBB =
      BasicBlock::Create(m->getContext(), "outer_loop.preheader", theFunction);
  BasicBlock *outerLoopBB =
      BasicBlock::Create(m->getContext(), "outer_loop", theFunction);
  BasicBlock *innerLoopBB =
      BasicBlock::Create(m->getContext(), "inner_loop", theFunction);
  BasicBlock *outerLoopBodyBB =
      BasicBlock::Create(m->getContext(), "outer_loop.body", theFunction);
  BasicBlock *returnBB =
      BasicBlock::Create(m->getContext(), "return", theFunction);

  // 入口
  builder.SetInsertPoint(entryBB);
  AllocaInst *jAlloca =
      builder.CreateAlloca(builder.getInt32Ty(), nullptr, "jAlloca");
  AllocaInst *iAlloca =
      builder.CreateAlloca(builder.getInt32Ty(), nullptr, "iAlloca");
  builder.CreateStore(builder.getInt32(0), iAlloca); // 初始i=0


  Value *cmp = builder.CreateICmpSLE(a2, builder.getInt32(1), "cmp");
  builder.CreateCondBr(cmp, returnBB, outerLoopPreheaderBB);

  // 外部循环前导
  builder.SetInsertPoint(outerLoopPreheaderBB);
  builder.CreateBr(outerLoopBB);

  // 外部循环
  builder.SetInsertPoint(outerLoopBB);
  builder.CreateStore(builder.getInt32(0), jAlloca); // 初始j=0
  Value *firstElement =
      builder.CreateLoad(ptrType, a1, "firstElement");
  Value *firstByte =
      builder.CreateTrunc(firstElement, builder.getInt8Ty(), "firstByte");
  builder.CreateBr(innerLoopBB);

  // 内部循环
  builder.SetInsertPoint(innerLoopBB);
  Value *jVal = builder.CreateLoad(builder.getInt32Ty(), jAlloca, "j");
  Value *a1Idx = builder.CreateGEP(builder.getInt8Ty(), a1, jVal, "a1.idx");
  Value *nextJVal = builder.CreateAdd(jVal, builder.getInt32(1), "j.next");
  builder.CreateStore(nextJVal, jAlloca);
  Value *a1IdxNext =
      builder.CreateGEP(builder.getInt8Ty(), a1, nextJVal, "a1.idx.next");
  Value *nextElement =
      builder.CreateLoad(builder.getInt8Ty(), a1IdxNext, "nextElement");
  builder.CreateStore(nextElement, a1Idx);
  Value *jCmp = builder.CreateICmpSLT(nextJVal, a2, "j.cmp");
  builder.CreateCondBr(jCmp, innerLoopBB, outerLoopBodyBB);

  // 外循环体
  builder.SetInsertPoint(outerLoopBodyBB);
  Value *shiftedFirstByteI64 =
      builder.CreateZExt(firstByte, builder.getInt8Ty(), "shiftedFirstByteI64");
  Value *lastIndex = builder.CreateSub(a2, builder.getInt32(1), "lastIndex");
  Value *a1LastPtr = builder.CreateGEP(builder.getInt8Ty(), a1, lastIndex, "a1.last.ptr");
  builder.CreateStore(shiftedFirstByteI64, a1LastPtr);
  Value *iVal = builder.CreateLoad(builder.getInt32Ty(), iAlloca, "i");
  Value *nextIVal = builder.CreateAdd(iVal, builder.getInt32(1), "i.next");
  builder.CreateStore(nextIVal, iAlloca); // 更新i的值
  Value *exitCond = builder.CreateICmpEQ(nextIVal, a3, "exitcond");
  builder.CreateCondBr(exitCond, returnBB, outerLoopBB);

  // 返回
  builder.SetInsertPoint(returnBB);
  //Value *retVal = builder.CreateSelect(
  //    cmp, builder.getInt64(0), builder.CreateZExt(a3, builder.getInt64Ty()),
  //    "retVal");
  //builder.CreateRet(retVal);
  builder.CreateRetVoid();

  //theFunction->print(outs());
  return theFunction;
}

void VariableRotation::processFunction(Function &f,
                                       const SetVector<Function *> &shift) {
  SetVector<AllocaInst *> list;
  for (BasicBlock &bb : f)
    for (Instruction &instr : bb)
      if (isa<AllocaInst>(instr)) {
        auto a = (AllocaInst *)(&instr);
        list.insert(a);
      }
  if (processVars(f, list, shift[0])) {
    for (AllocaInst *a : list)
      a->eraseFromParent();
  }
}

bool VariableRotation::processVars(Function &f, SetVector<AllocaInst *> &vars,
                                   Function *rotateFunc) {
  if (vars.size() < 2)
    return false;
  IRBuilder<> irb(&*f.getEntryBlock().getFirstInsertionPt());
  Value *zero = ConstantInt::get(irb.getInt32Ty(), 0);
  const auto data = f.getParent()->getDataLayout();
  int space = 0;
  SetVector<int> value_map;
  //printf("function: %s\n", f.getName().str().c_str());
  for (const auto a : vars) {
    value_map.insert(space);
    //printf("address:  %d\n", space);
    space += data.getTypeAllocSize(a->getAllocatedType());
  }
  ArrayType *array_type = ArrayType::get(irb.getInt8Ty(), space);
  AllocaInst *array = irb.CreateAlloca(array_type);
  for (BasicBlock &bb : f) {
    int offset = 0;
    auto iter = bb.getFirstInsertionPt();
    if (&bb == &f.getEntryBlock())
      ++iter;
    while (iter != bb.end()) {
      Instruction *inst = &*iter;
      irb.SetInsertPoint(inst);
      for (int i = 0; i < vars.size(); i++)
        if (isUsedByInst(inst, vars[i])) {
          if (constexpr int prob = 50;
              cryptoutils->get_uint32_t() % 100 < prob) {
            const int times =
                cryptoutils->get_uint32_t() % (vars.size() - 1) + 1;
            const int delta =
                (space + value_map[(offset + times) % vars.size()] -
                 value_map[offset]) %
                space;
            irb.CreateCall(
                FunctionCallee(rotateFunc),
                {irb.CreateGEP(array->getAllocatedType(), array, {zero, zero}),
                 ConstantInt::get(irb.getInt32Ty(), space),
                 ConstantInt::get(irb.getInt32Ty(), delta)});
            offset = (offset + times) % vars.size();
          }
          const int index = (space + value_map[i] - value_map[offset]) % space;
          Value *gep =
              irb.CreateGEP(array->getAllocatedType(), array,
                            {zero, ConstantInt::get(irb.getInt32Ty(), index)});
          Value *cast = irb.CreateBitOrPointerCast(gep, vars[i]->getType());
          int c = 0;
          for (const Value *ops : inst->operands()) {
            if (ops == vars[i])
              inst->setOperand(c, cast);
            c++;
          }
          break;
        }
      ++iter;
    }
    if (offset != 0) {
      irb.SetInsertPoint(bb.getTerminator());
      irb.CreateCall(
          FunctionCallee(rotateFunc),
          {irb.CreateGEP(array->getAllocatedType(), array, {zero, zero}),
           ConstantInt::get(irb.getInt32Ty(), space),
           ConstantInt::get(irb.getInt32Ty(),
                            (space - value_map[offset]) % space)});
    }
  }
  return true;
}

bool VariableRotation::isUsedByInst(Instruction *inst, const Value *var) {
  if (std::any_of(inst->operands().begin(), inst->operands().end(),
                  [&](const Value *in) { return in == var; })) {
    return true;
  }
  return false;
}

bool VariableRotation::runOnModule(Module &m) {

  Twine fname1 = Twine("shiftFuncitonI8");

  Function *shiftFunc =
      createRotateFunc(&m, PointerType::getUnqual(m.getContext()), fname1);

  SetVector<Function *> shifts;

  shifts.insert(shiftFunc);

  for (Function &f : m) {

    if (&f == shiftFunc)

      continue;

    if (f.hasExactDefinition())

      processFunction(f, shifts);
  }

  return true;
}

}


PreservedAnalyses VariableRotationPass::run(Module &M,
                                            ModuleAnalysisManager &AM) {
  if (RunVarRot) {
    VariableRotation varObf;
    if (varObf.runOnModule(M))
      return PreservedAnalyses::none();
  }
  return PreservedAnalyses::all();
}