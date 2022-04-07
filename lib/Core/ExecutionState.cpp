//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"

#include "klee/Expr.h"

#include "Memory.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#include "llvm/IR/CFG.h"
#endif

#include <iomanip>
#include <sstream>
#include <cassert>
#include <map>
#include <set>
#include <stdarg.h>

/* SYSREL extension */
#include "Executor.h"
#include "StatsTracker.h"
#include "llvm/IR/Module.h"
#include "MemoryManager.h"
/* SYSREL extension end */

using namespace llvm;
using namespace klee;

cl::opt<bool>
AvoidRedundantDFA("avoid-redundant-dfa",
         cl::desc("Avoid using redundant data-flow analysis (default false)\n"),
         cl::init(false));


cl::opt<unsigned>
StaticRelevanceDepth("static-relevance-depth",
         cl::desc("The maximum distance of CFG successors for deciding relevance of branches \n"),
         cl::init(1));

cl::opt<int>
MaxInterleavings("max-interleavings",
                cl::desc("Maximum number of thread interleavings per path (default 3)\n"),
                cl::init(3));

namespace { 
  cl::opt<bool>
  DebugLogStateMerge("debug-log-state-merge");
}

/* SYSREL */
extern KModule *kmoduleExt;
extern Interpreter *theInterpreter;
int ExecutionState::counter=0;
Sequential *LifeCycleModelState::lcm = NULL;
extern std::string entryFunctionName;
extern const Module * moduleHandle;

extern bool lazyInit;
extern bool lazySpec;
extern int numLazyInst;
extern std::set<std::string> lazyInits;
extern std::set<std::string> lazyInitSingles;
extern std::map<std::string, int> lazyInitNumInstances;

extern bool isLazyInit(Type *t, bool &single, int &count);
extern bool isAllocTypeLazyInit(Type *t, bool &single, int &count);
extern void copySingleOrDerivative(ExecutionState &to, const ExecutionState &from);
extern std::map<long, std::map<ref<Expr>, const MemoryObject *> > addressToMemObj;
extern std::map<long, std::map<ref<Expr>, ref<Expr> > > symIndexToMemBase;
extern std::map<long, std::map<std::string, unsigned> > forkFreqMapTrue;
extern std::map<long, std::map<std::string, unsigned> > forkFreqMapFalse;
extern std::map<long, std::map<long, unsigned int> > lazyInitConcreteAssumptions;
extern std::map<long, std::map<long, std::pair<std::string, unsigned> > > lazyInitEmbeddedPointers;
extern std::map<long, std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >,
                              ref<Expr> > > branchCondMap;
extern std::map<long, std::map<long, std::pair<std::string,
                                     std::vector<std::pair<Value*,ref<Expr> 
                              > > > > > memAllocMap;

extern std::map<long, 
               std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >,
                       std::set<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > > > 
               >
       > reverseVFG;

extern bool isATargetFunction(std::string f);

extern std::map<long, bool> watchOnGlobal;
extern std::map<long, std::map<long, WPState*> > wpMap;

/* WEIGHTS */
std::map<std::string, double> failureStackTrace;
std::map<std::string, double> normalStackTrace;
std::map<std::string, double> overallStackTrace;
std::map<std::string, double> failureConstraint;
std::map<std::string, double> normalConstraint;
std::map<std::string, double> overallConstraint;
std::map<std::string, std::string> attributeType;
/* WEIGHTS */
/* SYSREL */

/***/

unsigned WPState::count = 0;

WPState::WPState() {
  id = count++;
  children = new std::vector<long>();
  args = new std::vector<ref<Expr> >();
  ki = NULL;
  parent = NULL;
  type = new std::string("init");
  numChildrenCompleted = 0;
  mo = NULL;
  parent = NULL;
}

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0), 
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
  lastCallIndex = -1;
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
  lastCallIndex = s.lastCallIndex ;
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

/***/

double ExecutionState::CustomWeightThreshold = 0;
std::string ExecutionState::CustomWeightType = "overall";

ExecutionState::ExecutionState(KFunction *kf) :
    pc(kf->instructions),
    prevPC(pc),

    queryCost(0.), 
    weight(1),
    depth(0),

    instsSinceCovNew(0),
    coveredNew(false),
    forkDisabled(false),
    ptreeNode(0),
    steppedInstructions(0) {
   /* SYSREL */
  lastAccessedAddr = NULL;
  lastAccessedMem = NULL;
  interleavingDelayed = false;
  cancelled = false;
  currentwps = new WPState();
  numInterleavings = 0;
  activeInferenceForExecuted = true;
  activeInferenceForToBeExecuted = true;
  terminated = false;
  pushFrame(0, kf);
  /* SYSREL */
  //threadsQueue.push(-1);
  pathCompleted = false;
  instThreadIdMap = NULL; // not meant to be copied
  rtid = -1;
  lastSegmentStartIndex = 0;
  waitingForThreadsToTerminate = false;
  id = counter++;
  if (LifeCycleModelState::lcm)
    lcmState = new LifeCycleModelState();
  else lcmState = NULL;
  pmstack.clear();
  std::map<ref<Expr>, ref<Expr> > em1;
  symIndexToMemBase[(long)this] = em1;
  std::map<ref<Expr>, const MemoryObject*> em2;
  addressToMemObj[(long)this] = em2;
  std::map<std::string, unsigned> fm;
  forkFreqMapTrue[(long)this] = fm;
  forkFreqMapFalse[(long)this] = fm;
  std::map<long, unsigned int> mm;
  lazyInitConcreteAssumptions[(long)this] = mm;
  std::map<long, std::pair<std::string, unsigned> > me;
  lazyInitEmbeddedPointers[(long)this] = me;
  std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >, ref<Expr> > mb;
  branchCondMap[(long)this] = mb;
  std::map<long, std::pair<std::string,
                          std::vector<std::pair<Value*,ref<Expr> > > > > ma;
  memAllocMap[(long)this] = ma;
  std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >,
                       std::set<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > > >
               > mg;
  reverseVFG[(long)this] = mg; 
  lastMallocedMem = NULL;
  lastContext = "";
  stackFrameBeforeExecInst = -1;
  lastConstraint = NULL;
  lastBranchInstConstraint = NULL;
  /* SYSREL */  
}

ExecutionState::ExecutionState(const std::vector<ref<Expr> > &assumptions)
    : constraints(assumptions), queryCost(0.), ptreeNode(0) {
   /* SYSREL */
  lastAccessedAddr = NULL;
  lastAccessedMem = NULL;
  interleavingDelayed = false;
  cancelled = false;
  currentwps = new WPState();
  numInterleavings = 0;
  activeInferenceForExecuted = true;
  activeInferenceForToBeExecuted = true;
  terminated = false;
  //threadsQueue.push(-1);
  pathCompleted = false;
  instThreadIdMap = NULL; // not meant to be copied
  rtid = -1;
  lastSegmentStartIndex = 0;
  waitingForThreadsToTerminate = false;
  id = counter++;
  if (LifeCycleModelState::lcm)
    lcmState = new LifeCycleModelState();
  pmstack.clear();
  std::map<ref<Expr>, ref<Expr> > em1;
  symIndexToMemBase[(long)this] = em1;
  std::map<ref<Expr>, const MemoryObject*> em2;
  addressToMemObj[(long)this] = em2;
  std::map<std::string, unsigned> fm;
  forkFreqMapTrue[(long)this] = fm;
  forkFreqMapFalse[(long)this] = fm;
  std::map<long, unsigned int> mm;
  lazyInitConcreteAssumptions[(long)this] = mm;
  std::map<long, std::pair<std::string, unsigned> > me;
  lazyInitEmbeddedPointers[(long)this] = me;
  std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >, ref<Expr> > mb;
  branchCondMap[(long)this] = mb;
  std::map<long, std::pair<std::string,
                          std::vector<std::pair<Value*,ref<Expr> > > > > ma;
  memAllocMap[(long)this] = ma;
  std::map<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > >,
                       std::set<std::pair<std::string,std::vector<std::pair<Value*,ref<Expr> > > > >
               > mg;
  reverseVFG[(long)this] = mg; 
  lastMallocedMem = NULL;
  lastContext = "";
  stackFrameBeforeExecInst = -1;
  lastConstraint = NULL;
  lastBranchInstConstraint = NULL;
  /* SYSREL */  
}

/* SYSREL */
void ExecutionState::extendExecutionWith(KFunction *kf) {
  KInstIterator temp(kf->instructions);
  pc = temp;
  prevPC = pc;
  CallPathNode *prev = stack.back().callPathNode;
  popFrame(); // removes the locals of the previous function
  pushFrame(0, kf);
  stack.back().callPathNode = prev; 
  // allocate symbolic arguments
  bool abort = false;
  ((Executor*)theInterpreter)->initArgsAsSymbolic(*this, kf->function, abort);
  assert(!abort);
  llvm::outs() << "extending execution with the first instruction \n";
  pc->inst->print(llvm::outs());
}
/* SYSREL */

ExecutionState::~ExecutionState() {
  for (unsigned int i=0; i<symbolics.size(); i++)
  {
    const MemoryObject *mo = symbolics[i].first;
    assert(mo->refCount > 0);
    mo->refCount--;
    if (mo->refCount == 0)
      delete mo;
  }

  for (auto cur_mergehandler: openMergeStack){
    cur_mergehandler->removeOpenState(this);
  }


  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    fnAliases(state.fnAliases),
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),

    addressSpace(state.addressSpace),
    constraints(state.constraints),

    queryCost(state.queryCost),
    weight(state.weight),
    depth(state.depth),

    pathOS(state.pathOS),
    symPathOS(state.symPathOS),

    instsSinceCovNew(state.instsSinceCovNew),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    coveredLines(state.coveredLines),
    ptreeNode(state.ptreeNode),
    symbolics(state.symbolics),
    arrayNames(state.arrayNames),
    openMergeStack(state.openMergeStack),
    steppedInstructions(state.steppedInstructions)
{
  for (unsigned int i=0; i<symbolics.size(); i++)
    symbolics[i].first->refCount++;

  for (auto cur_mergehandler: openMergeStack)
    cur_mergehandler->addOpenState(this);

  /* SYSREL */
  scheduledIP = state.scheduledIP;
  lastAccessedAddr = state.lastAccessedAddr;
  lastAccessedMem = state.lastAccessedMem;
  interleavingDelayed = state.interleavingDelayed;
  cancelled = state.cancelled;
  currentwps = NULL;
  //lastkimap = state.lastkimap;
  if (watchOnGlobal.find((long)&state) != watchOnGlobal.end())
     watchOnGlobal[(long)this] = watchOnGlobal[(long)&state];
  sharedObjects = state.sharedObjects;
  threadsWaitingOnObject = state.threadsWaitingOnObject;
  threadsReleasingObjectWhileWaitingOnObject = state.threadsReleasingObjectWhileWaitingOnObject;
  IPMap = state.IPMap;
  for(auto se: state.StoreValue)
     StoreValue[se.first] = se.second;
  numInterleavings = 0;/*state.numInterleavings;*/
  activeInferenceForExecuted = state.activeInferenceForExecuted;
  activeInferenceForToBeExecuted = state.activeInferenceForToBeExecuted;
  releaseObjMap = state.releaseObjMap;
  acquireObjMap = state.acquireObjMap;
  joinObjMap = state.joinObjMap;
  globals = state.globals;
  memobjMap = state.memobjMap;
  valueMap = state.valueMap;
  likelyRelevantBranches = state.likelyRelevantBranches;
  terminated = state.terminated;
  threadsQueue = state.threadsQueue; 
  pathCompleted = state.pathCompleted; 
  instThreadIdMap = NULL; // not meant to be copied
  rtid = state.rtid;
  Path = state.Path;
  KPath = state.KPath;
  PathMemObject = state.PathMemObject;
  PathValueObject = state.PathValueObject;
  writeMap = state.writeMap;
  readMap = state.readMap;
  threadSchedulePoints = state.threadSchedulePoints;
  lastSegmentStartIndex = state.lastSegmentStartIndex;
  threadIdMap = state.threadIdMap; 
  threadIdObjMap = state.threadIdObjMap; 
  threadCreationMap = state.threadCreationMap;
  //targetObjects = state.targetObjects;
  //targetInstructions = state.targetInstructions;
  blockedThreads = state.blockedThreads;
  threadsBlockedOnObject = state.threadsBlockedOnObject;
  threadsBlockedForJoining = state.threadsBlockedForJoining;
  waitingForThreadsToTerminate = state.waitingForThreadsToTerminate;
  for(unsigned int i=0; i < state.threads.size(); i++) {
     threads.push_back(state.threads[i]);
     Async &a = threads[i];
     a.context = this;
  }
  id = counter++;
  if (LifeCycleModelState::lcm)
    lcmState = new LifeCycleModelState(*state.lcmState);
  typeToAddr = state.typeToAddr;
  addrToCastFromStructType = state.addrToCastFromStructType;
  refCountModel = state.refCountModel;
  refCountStack = state.refCountStack;
  symbolDefs = state.symbolDefs;
  symbolTypes = state.symbolTypes;
  symIdCounters = state.symIdCounters;
  lazyInitSingleInstances = state.lazyInitSingleInstances;
  for(auto pmf : pmstack) 
     pmstack.push_back(new PMFrame(*pmf));
  metadataMap = state.metadataMap; 
  copySingleOrDerivative(*this, state);
  if (symIndexToMemBase.find((long)&state) != symIndexToMemBase.end())
    symIndexToMemBase[(long)this] = symIndexToMemBase[(long)&state];
  if (addressToMemObj.find((long)&state) != addressToMemObj.end())
    addressToMemObj[(long)this] = addressToMemObj[(long)&state];
  if (forkFreqMapTrue.find((long)&state) != forkFreqMapTrue.end())
     forkFreqMapTrue[(long)this] = forkFreqMapTrue[(long)&state];
  if (forkFreqMapFalse.find((long)&state) != forkFreqMapFalse.end())
     forkFreqMapFalse[(long)this] = forkFreqMapFalse[(long)&state];
  if (lazyInitConcreteAssumptions.find((long)&state) !=  lazyInitConcreteAssumptions.end())
     lazyInitConcreteAssumptions[(long)this] = lazyInitConcreteAssumptions[(long)&state];
  if (lazyInitEmbeddedPointers.find((long)&state) != lazyInitEmbeddedPointers.end())
     lazyInitEmbeddedPointers[(long)this] = lazyInitEmbeddedPointers[(long)&state];
  if (branchCondMap.find((long)&state) != branchCondMap.end())
     branchCondMap[(long)this] = branchCondMap[(long)&state];
  if (memAllocMap.find((long)&state) != memAllocMap.end())
     memAllocMap[(long)this] = memAllocMap[(long)&state];
  if (reverseVFG.find((long)&state) != reverseVFG.end())
     reverseVFG[(long)this] = reverseVFG[(long)&state]; 
  lastMallocedMem = state.lastMallocedMem;
  lastContext = state.lastContext;
  stackFrameBeforeExecInst = state.stackFrameBeforeExecInst;
  lastConstraint = state.lastConstraint; 
  lastBranchInstConstraint = state.lastBranchInstConstraint;
  llvm::errs() << "copying fro other state, size=" << state.lastValuedInst.size() << "\n";
  for(unsigned int i=0; i<state.lastValuedInst.size(); i++) {
     std::pair<Value*,ref<Expr> > p = state.lastValuedInst[i];
     lastValuedInst.push_back(p);
  }
  /* SYSREL */ 
}

bool ExecutionState::isInterleavingDelayed() {
   return interleavingDelayed;
}

void ExecutionState::setInterleavingDelayed(bool value) {
  interleavingDelayed = value;
}

ExecutionState *ExecutionState::branch() {
  depth++;

  ExecutionState *falseState = new ExecutionState(*this);
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  weight *= .5;
  falseState->weight -= weight;

  return falseState;
}

void ExecutionState::matchReturnGetOperands(ref<Expr> retVal, 
                                            std::set<ref<Expr> > &ops) {
  for(auto mopinst : PathValueObject) {
     for(auto mop : mopinst.second) {
        if (mop.first == -1 && mop.second == retVal) {
           for(auto opsm : mopinst.second)
              if (opsm.first != -1)      
                 ops.insert(opsm.second);
        }
     }
  }  
}

void ExecutionState::updateLikelyRelevantBranches(int index, int br) { 
   likelyRelevantBranches.insert(std::make_pair(index, br));    
}

bool ExecutionState::isRelevantInstruction(Instruction *inst, Function *&calledf) {
  if (inst->getOpcode() == Instruction::Call || 
      inst->getOpcode() == Instruction::Invoke) {
      CallSite cs(&(*inst));
      Value *fp = cs.getCalledValue();
      Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
      if (isATargetFunction(f->getName()))   
         return true;
      else 
         calledf = f;
  }
  else if (inst->getOpcode() == Instruction::Store ) {
     StoreInst *si = dyn_cast<StoreInst>(inst);
     Type *t = si->getOperand(1)->getType();
     if (t->isPointerTy()) {
        t = t->getPointerElementType();
        if (t->isPointerTy()) 
           return true;
     }
  }  
  else if (inst->getOpcode() == Instruction::Load) {
     LoadInst *li = dyn_cast<LoadInst>(inst);
     Type *t = li->getOperand(0)->getType();
     if (t->isPointerTy()) {
        t = t->getPointerElementType();
        if (t->isPointerTy()) 
           return true;
     }  
  }  
  return false;
}

bool ExecutionState::isLikelyRelevantInstructionDepth(BasicBlock *bb, 
                                         std::set<BasicBlock*> &visited, int depth) {
  visited.insert(bb);
  for(BasicBlock::iterator i=bb->begin(); i!=bb->end(); i++) {
     llvm::errs() << "Checking instruction on alternative branch target: " 
                  << (*i) << "\n";
     Function *cf = NULL;
     bool rel = isRelevantInstruction(&(*i), cf);
     if (rel) return true;
     if (cf && !cf->isDeclaration()) {
        // Analyze the function body
        llvm::errs() << "Analyzing the function entry of " << cf->getName() << "\n";
        BasicBlock &eb = cf->getEntryBlock();
        if (depth < StaticRelevanceDepth && visited.find(&eb) == visited.end()) {
           bool frel = isLikelyRelevantInstructionDepth(&eb, visited, depth + 1);
           if (frel) return true;
        }
     }
  }
  for(succ_iterator it=	succ_begin(bb); it != succ_end(bb); it++) {
     if (depth < StaticRelevanceDepth && visited.find(*it) == visited.end()) {
        bool br = isLikelyRelevantInstructionDepth(*it, visited, depth + 1);
        if (br) return true;
     }
  }   
  return false;
}


bool ExecutionState::isLikelyRelevantInstruction(int index, int br) {
  createInstThreadMap();
  std::pair<Instruction*, std::string> p = Path[index];
  BranchInst *brc = dyn_cast<BranchInst>(p.first);
  BasicBlock *bb = brc->getSuccessor(br);
  std::set<BasicBlock*> visited;
  return isLikelyRelevantInstructionDepth(bb, visited, 1);
  /*
  for(BasicBlock::iterator i=bb->begin(); i!=bb->end(); i++) {
     llvm::errs() << "Checking instruction on alternative branch target: " 
                  << (*i) << "\n";
     if (i->getOpcode() == Instruction::Call || 
         i->getOpcode() == Instruction::Invoke) {
         CallSite cs(&(*i));
         Value *fp = cs.getCalledValue();
         Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
         if (isATargetFunction(f->getName()))   
            return true;
     }
     else if (i->getOpcode() == Instruction::Store ) {
        StoreInst *si = dyn_cast<StoreInst>(i);
        Type *t = si->getOperand(1)->getType();
        if (t->isPointerTy()) {
            t = t->getPointerElementType();
            if (t->isPointerTy()) 
               return true;
        } 
     }
     else if (i->getOpcode() == Instruction::Load) {
        LoadInst *li = dyn_cast<LoadInst>(i);
        Type *t = li->getOperand(0)->getType();
        if (t->isPointerTy()) {
            t = t->getPointerElementType();
            if (t->isPointerTy()) 
               return true;
        }  
     }
  }  
  return false;
   */
} 

void ExecutionState::getValues(int index, 
               std::set<Instruction*> &values, unsigned minoperand, 
               bool returnVal) {
   std::pair<Instruction*, std::string> pair = Path[index];
   Instruction *inst = pair.first;
   for(unsigned i=0; i<inst->getNumOperands(); i++) {
      if (i>=minoperand) {
         Value *v = inst->getOperand(i);
         if (isa<Instruction>(*v)) {
            Instruction *oi = (Instruction*)v;
            values.insert(oi);
         }
      }
   }
   if (returnVal)
      values.insert(inst);
/*
   std::map<std::string, std::map<int, ref<Expr> > > vm;
   std::pair<Instruction*, std::string> pair = Path[index];
   Instruction *inst = pair.first;
   std::string ctx = pair.second;
   llvm::errs() << "Get values for index " << index << " inst " << (*inst) 
                << " minop: " << minoperand 
                << "retval?" << returnVal  
                << " address=" << &PathValueObject << "\n"; 
   if (PathValueObject.find(index) != PathValueObject.end()) 
   {
      llvm::errs() << "checking entry for index: " << index << "\n";
      std::map<int, ref<Expr> >  vl = PathValueObject[index];
      //vm = PathValueObject[inst];
      //if (vm.find(ctx) != vm.end())
      //   vl = vm[ctx];
      for(auto vle : vl) {
         llvm::errs() << vle.first << "->" << vle.second << "\n";
         if (vle.first >= 0) {
            if (vle.first >= minoperand) {
               values.insert(vle.second);
               llvm::errs() << "op: " << vle.first << " value " << vle.second << "\n";
            }
         }
         else {
            if (returnVal) {
               values.insert(vle.second);     
               llvm::errs() << " return value " << vle.second << "\n";
            }
         }
      }
   }
*/
}

bool ExecutionState::getMemObjects(ref<Expr> value, 
                                   std::set<long> &objects,
                                   std::set<int> &relevantInst) {
  llvm::errs() << "Searching for memobject of value " << value << "\n";
  bool found = false;
  for(auto im : PathMemObject) {
     for(auto mop : im.second) {
        if (mop.first == value) {
           found = true;
           objects.insert(mop.second);
           relevantInst.insert(im.first);
           /*std::pair<Instruction*, std::string> mopinst = Path[im.first];
           if (mopinst.first->getOpcode() == Instruction::Load)
              recordObjectAction(readMap, mop.second, im.first); 
           else if (mopinst.first->getOpcode() == Instruction::Store)
              recordObjectAction(writeMap, mop.second, im.first); */
        }
     }
  }
  return found;
}

void ExecutionState::getMemObjectsAll(ref<Expr> value, 
                                      std::set<long> &objects,
                                      std::set<int> &relevantInst) {
  if (!getMemObjects(value, objects, relevantInst))
     return;
  std::vector<ref<Expr> > worklist;
  worklist.push_back(value); 
  while(worklist.size() > 0) {
     std::set<ref<Expr> > ops;
     ref<Expr> rv = worklist.back();
     worklist.pop_back();
     matchReturnGetOperands(rv, ops);
     for(auto op : ops) {
        if (!getMemObjects(op, objects, relevantInst))
           worklist.push_back(op);
     }
  }
}

void ExecutionState::processGep(int index, 
                                std::set<long> &objects,
                                std::set<int> &relevantInst) {
   std::set<Instruction*> opvals;
   // collect values of the indices 
   // (we interpreted those as op nos starting from one)
   int tid = (*instThreadIdMap)[index]; 
   getValues(index, opvals, 1, false);
   for(auto v : opvals)
      getSourceMemObjects(index-1, v, objects, relevantInst, tid);
}

void ExecutionState::processTargetCall(int index, 
                                 std::set<long> &objects,
                                 std::set<int> &relevantInst,
           std::set<std::pair<Instruction*, std::string> > &IP, 
                                 bool args, bool ret) {
   std::set<Instruction*> opvals;
   std::pair<Instruction*, std::string> pair = Path[index];
   if (!(pair.first->getOpcode() == Instruction::Call || 
         pair.first->getOpcode() == Instruction::Invoke))
      return; 
   CallSite cs(pair.first);
   Value *fp = cs.getCalledValue();
   Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
   if (f && isATargetFunction(f->getName())) {
      // collect the actual argument values and then the objects
      relevantInst.insert(index);
      // Record free and write as write operations
      if (f->getName() == "free" || f->getName() == "malloc") {
         IP.insert(Path[index]);
         if (PathMemObject.find(index) != PathMemObject.end() && 
                      !PathMemObject[index].empty()) {
            llvm::errs() << "Malloc/free: " << (*pair.first) << "\n";
            for(auto om : PathMemObject[index])  {
               llvm::errs() << "\t\t object: " << om.second << "\n";
               objects.insert(om.second);
            }
         }   
      }
      int tid = (*instThreadIdMap)[index]; 
      int min = 0;
      if (!args) 
         min = cs.arg_size();
      getValues(index, opvals, min, ret);
      for(auto v : opvals)
         getSourceMemObjects(index-1, v, objects, relevantInst, tid);
   }
}

void ExecutionState::processCall(int index, 
                                 std::set<long> &objects,
                                 std::set<int> &relevantInst, 
                                 std::string name, bool args, bool ret) {
   std::set<Instruction*> opvals;
   std::pair<Instruction*, std::string> pair = Path[index];
   if (!(pair.first->getOpcode() == Instruction::Call || 
         pair.first->getOpcode() == Instruction::Invoke))
      return; 
   CallSite cs(pair.first);
   Value *fp = cs.getCalledValue();
   Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
   if (f && f->getName() == name) {
      if (name == "malloc") {
         if (PathMemObject.find(index) != PathMemObject.end() && 
                      !PathMemObject[index].empty()) {
            for(auto om : PathMemObject[index]) {
               objects.insert(om.second);
               relevantInst.insert(index);
            }
         }
         return;
      }
      // collect the actual argument values and then the objects
      int tid = (*instThreadIdMap)[index]; 
      int min = 0;
      if (!args) 
         min = cs.arg_size();
      getValues(index, opvals, min, ret);
      for(auto v : opvals)
         getSourceMemObjects(index-1, v, objects, relevantInst, tid);
   }
}

void ExecutionState::processMallocs(int max, 
                                    std::set<long> &objects,
                                    std::set<int> &relevantInst)  {
   for(unsigned i=0; i < max; i++) 
      processCall(i, objects, relevantInst, "malloc", false, true);
}

void ExecutionState::recordObjectAction(std::map<long, 
                                    std::map<int, std::set<int> > > &rwmap, 
                                        long obj, int index) {
   std::map<int, std::set<int> > m1;
   if (rwmap.find(obj) != rwmap.end()) 
      m1 = rwmap[obj];
   std::set<int> m2;
   int tid = (*instThreadIdMap)[index]; 
   if (m1.find(tid) != m1.end())
      m2 = m1[tid];
   m2.insert(index);
   m1[tid] = m2;
   rwmap[obj] = m1;
   //llvm::errs() << "Recording r/w action by thread " << tid 
   //             << " on object " << obj 
   //             << " at inst " << (*Path[index].first) << "\n";
}
 
bool ExecutionState::storedInGlobal(long mo, int min, int max) {
  for(unsigned i=min; i<=max; i++) {
     std::pair<Instruction*,std::string> p = Path[i];
     Instruction* inst = p.first;     
     if (inst->getOpcode() == Instruction::Store) {
        assert(StoreValue.find(i) != StoreValue.end());
        ref<Expr> v = StoreValue[i];
        llvm::errs() << "value from store " << (*p.first) << ": " << (*v) << "\n";
        ConstantExpr * CE = dyn_cast<ConstantExpr>(v);
        if (CE && CE->getWidth() <= 64) {
           if (mo == CE->getZExtValue()) {
              if (PathMemObject.find(i) != PathMemObject.end()) {
                 for(auto ga : PathMemObject[i])
                    if (globals.find(ga.second) != globals.end())
                       return true;  
              }
           }
        }
     }     
  }
  return false;    
}


bool ExecutionState::addressFlowsInto(long smo, long dmo, int min, int max) {
   for(unsigned i=min; i<=max; i++) {
     std::pair<Instruction*,std::string> pair = Path[i];
     Instruction* inst = pair.first;     
     if (inst->getOpcode() == Instruction::Store) {
        assert(StoreValue.find(i) != StoreValue.end());
        ref<Expr> v = StoreValue[i];
        ConstantExpr * CE = dyn_cast<ConstantExpr>(v);
        if (CE && CE->getWidth() <= 64) {
           if (smo == CE->getZExtValue()) {  
              if (PathMemObject.find(i) != PathMemObject.end()) {
                 for(auto dob : PathMemObject[i]) {
                    if (dob.second == dmo)
                       return true;
                    if (addressFlowsInto(dob.second, dmo, i+1, max))
                       return true;                       
                 }
              }
           }
        } 
     }
   }  
   return false; 
}

bool ExecutionState::flowsIntoThreadCreate(long mo, int min, int max) {
   for(unsigned i=min; i<=max; i++) {
     std::pair<Instruction*,std::string> pair = Path[i];
     Instruction* inst = pair.first;     
     if (inst->getOpcode() == Instruction::Call || 
         inst->getOpcode() == Instruction::Invoke) {
        CallSite cs(inst);
        Value *fp = cs.getCalledValue();
        Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
        if (f && f->getName() ==  "pthread_create") {
           if (PathValueObject.find(i) != PathValueObject.end()) {
              ref<Expr> arg3 = PathValueObject[i][3];
              ConstantExpr *CE = dyn_cast<ConstantExpr>(arg3);
              if (CE && CE->getZExtValue() == mo)
                 return true;
              if (addressFlowsInto(mo, CE->getZExtValue(), 0, i-1))
                 return true;   
           } 
        }       
     }
   }
   return false;
}

bool ExecutionState::localAddressEscapes(long mo, int max) {
  // Find addresses produced by alloca instructions
  std::set<long> allocas;
  for(unsigned i=0; i<=max; i++) {
     std::pair<Instruction*,std::string> pair = Path[i];
     Instruction* inst = pair.first;     
     if (inst->getOpcode() == Instruction::Alloca) {
        if (PathMemObject.find(i) != PathMemObject.end()) {
           for(auto moe : PathMemObject[i]) {
              if (moe.second == mo && (storedInGlobal(mo, i+1, max) || 
                               flowsIntoThreadCreate(mo, i+1, max))) 
                 return true;
           }
        }
     }
  }
  return false;   
}

void ExecutionState::processNonLocalPointerAccess(int index, 
                         std::set<long> &objects,
                         std::set<int> &relevantInst)  {
   bool pointer = false;
   std::pair<Instruction*,std::string> pair = Path[index];
   Instruction* i = pair.first;
   if (i->getOpcode() == Instruction::Store ) {
      StoreInst *si = dyn_cast<StoreInst>(i);
      Type *t = si->getOperand(1)->getType();
      if (t->isPointerTy()) {
         t = t->getPointerElementType();
         if (t->isPointerTy()) 
            pointer = true;
      } 
   }
   else if (i->getOpcode() == Instruction::Load ) {
      LoadInst *si = dyn_cast<LoadInst>(i);
      Type *t = si->getOperand(0)->getType();
      if (t->isPointerTy()) {
         t = t->getPointerElementType();
         if (t->isPointerTy()) 
            pointer = true;
      } 
   }
   //if (pointer) {
      if (PathMemObject.find(index) != PathMemObject.end()) {
         std::map<ref<Expr>, long> mom = PathMemObject[index];
         for(auto m : mom) {
            if (sharedObjects.find(m.second) != sharedObjects.end() || 
                  globals.find(m.second) != globals.end() || 
                     localAddressEscapes(m.second, index-1)) {
               llvm::errs() << "adding global obj/escaping local " << m.second 
                            << " and access inst " 
                            << (*i) << "\n";
               objects.insert(m.second);
               relevantInst.insert(index); 
            }
         }
      }
   //}
   

} 

void ExecutionState::processLoadFromHeap(int index, 
                         std::set<long> &objects,
                         std::set<int> &relevantInst)  {
   std::set<long> o1;
   std::set<int> r1;
   llvm::errs() << "Is load from heap" << (*Path[index].first) << "\n";
   processMallocs(index,o1,r1);
   llvm::errs() << "Malloc objects: " << o1.size() << "\n";
   for(auto o1e : o1)
      llvm::errs() << "\t" << o1e << "\n";
   std::set<Instruction*> opvals;
   // get the return value and then the corresponding objects
   std::set<long> o2;
   std::set<int> r2;
   int tid = (*instThreadIdMap)[index]; 
   getValues(index, opvals, 0, true); 
   llvm::errs() << "Load values: " << opvals.size() << "\n";
   for(auto v : opvals)
      getSourceMemObjects(index-1, v, o2, r2, tid);
   if (PathMemObject.find(index) != PathMemObject.end()) {
      std::map<ref<Expr>, long> mom = PathMemObject[index];
      for(auto m : mom) 
         o2.insert(m.second);
   }
   llvm::errs() << "Load objects: " << o2.size() << "\n";
   for(auto o2e : o2)
      llvm::errs() << "\t" << o2e << "\n";
   for(auto ob2: o2) {
      if (o1.find(ob2) != o1.end()) {
         objects.insert(ob2);
         relevantInst.insert(index); // some wastage, who cares?
         recordObjectAction(readMap, ob2, index);
         llvm::errs() << "Process load from heap " << (*Path[index].first) << "\n";
      }
   }
}

void ExecutionState::collectDirectTargetObjectsInstructions(
                                  std::set<long> &objects,
                                  std::set<int> &relevantInst, 
            std::set<std::pair<Instruction*, std::string> > &IP) {
   std::set<ref<Expr> > worklist;
   for(unsigned i=0; i<Path.size(); i++) {
      std::pair<Instruction*, std::string> pair = Path[i];
      switch (pair.first->getOpcode()) {
          case Instruction::GetElementPtr: {
               processGep(i, objects, relevantInst); 
               break;
          }
          case Instruction::Invoke:
          case Instruction::Call: {               
               processCall(i, objects, relevantInst, "free", true, false); 
               processTargetCall(i, objects, relevantInst, IP, true, false); 
               break;
          }
          case Instruction::Load: {
               processLoadFromHeap(i, objects, relevantInst);
               // if non-local double pointer..
               processNonLocalPointerAccess(i, objects, relevantInst);
          }
          case Instruction::Store: {
               // if non-local double pointer..
               processNonLocalPointerAccess(i, objects, relevantInst);
               break;
          }
          default: break;
      }
   }

}


void ExecutionState::collectPrecedingBranches(int index, int tid, 
                                              std::set<int> &br) {
   for(auto tsp : threadSchedulePoints) {
      if (tsp.second.first == tid && tsp.second.second < index) {
         for(unsigned i=tsp.first; i<= tsp.second.second; i++) {
            std::pair<Instruction*, std::string>  pair = Path[i];
            if (pair.first->getOpcode() == Instruction::Br) {
               BranchInst *bi = cast<BranchInst>(pair.first);
               if (!bi->isUnconditional()) 
                  br.insert(i);
            }
         }
          
      }
   }
}

int ExecutionState::getThreadIdForIndex(int index) {
   for(auto tsp : threadSchedulePoints) {
      if (index >= tsp.first && index <= tsp.second.second)
         return tsp.second.first;
   }
   return -1; 
}

/*void ExecutionState::getMatchingPathIndices(std::pair<Instruction*, std::string> pair, 
                            std::set<int> &indices) {
   for(unsigned i=0; i<Path.size(); i++)
      if (Path[i] == pair)
         indices.insert(i);
}*/

void ExecutionState::propagateControlFlow(int index,
                                          std::set<long> &objects,
                                          std::set<int> &relevantInst, 
                                          std::set<long> &nobjects,
                                          std::set<int> &nrelevantInst) {
   // find out all preceding conditional branch instructions that have been 
   // executed by the same thread and find the objects related to the 
   // conditions
   //std::pair<Instruction*, std::string> pair = Path[index]; 
   //Instruction *inst = pair.first;
   //std::string ctx = pair.second;
   std::set<int> branches;
   int tid = (*instThreadIdMap)[index];
   collectPrecedingBranches(index, tid, branches); 
   llvm::errs() << "Number of preceding branches: " 
                << branches.size() << "\n"; 
   for(auto br : branches) {
      std::set<Instruction*> opvals;
      getValues(index, opvals, 0, false);
      for(auto op : opvals) {
         std::set<long> to;
         std::set<int> tr;
         getSourceMemObjects(index-1, op, to, tr, tid);
         for(auto tobj : to) {
            if (objects.find(tobj) == objects.end())
               nobjects.insert(tobj);
         } 
         for(auto tri : tr) {
            if (relevantInst.find(tri) == relevantInst.end())
               nrelevantInst.insert(tri); 
         }
      }
   }  
}

long ExecutionState::getMemoryObjectForLoadStore(int index) {
   std::pair<Instruction*, std::string> pair = Path[index];
   if (pair.first->getOpcode() == Instruction::Store || 
          pair.first->getOpcode() == Instruction::Load) {
      if (PathMemObject.find(index) != 
                           PathMemObject.end()) {
         std::map<ref<Expr>, long> m = PathMemObject[index];
         assert(m.size() <= 1 && 
                 "Load/Store cannot be mapped to more than one object!\n");
         for(auto mp : m) 
            return mp.second;         
      }
   }
   return NULL;
}

bool ExecutionState::collectMostRecentWrite(int index, int tid, 
                                            int &write) {
   if (index <= 0) return false;
   std::pair<Instruction*, std::string>  p1 = Path[index];
   long mo1 = getMemoryObjectForLoadStore(index); 
   for(int i=index-1; i >=0 ; i--) {
      int tid2 = (*instThreadIdMap)[i];
      if (tid2 == tid) {
         std::pair<Instruction*, std::string>  pair = Path[i];
         if (pair.first->getOpcode() == Instruction::Store) {
            long mo2 = getMemoryObjectForLoadStore(i);
            if (mo1 == mo2) {
                write = i;
                return true;
            }      
         }
      }
   }
   return false;

}

void ExecutionState::propagateDataFlow(int index,
                                       std::set<long> &objects,
                                       std::set<int> &relevantInst, 
                                       std::set<long> &nobjects,
                                       std::set<int> &nrelevantInst) {
   std::pair<Instruction*, std::string> pair = Path[index];
   Instruction *inst = pair.first;
   if (inst->getOpcode() != Instruction::Load)
      return;
   int write;
   int tid = (*instThreadIdMap)[index];   
   if (collectMostRecentWrite(index, tid, write)) {
      nrelevantInst.insert(write);
   }
}

void ExecutionState::recordObjectActions(std::set<long> &objects) {
   for(int i=0; i<Path.size(); i++) {
      if (PathMemObject.find(i) != PathMemObject.end() && 
          !PathMemObject[i].empty()) {
          for(auto om : PathMemObject[i]) {
             if (objects.find(om.second) != objects.end()) {
                std::pair<Instruction*, std::string> mopinst = Path[i];
                if (mopinst.first->getOpcode() == Instruction::Load)
                   recordObjectAction(readMap, om.second, i); 
                else if (mopinst.first->getOpcode() == Instruction::Store)
                   recordObjectAction(writeMap, om.second, i);
                else if (mopinst.first->getOpcode() == Instruction::Call || 
                         mopinst.first->getOpcode() == Instruction::Invoke) {
                   CallSite cs(mopinst.first);
                   Value *fp = cs.getCalledValue();
                   Function *f = ((Executor*)theInterpreter)->getTargetFunction(fp, *this);
                   if (f && (f->getName() == "malloc" || f->getName() == "free")) 
                      recordObjectAction(writeMap, om.second, i);
                }
            }
                
          }
      }
   } 
}

void ExecutionState::getSourceMemObjects(int index, Instruction *inst, 
                                         std::set<long> &objects,
                                         std::set<int> &relevantInst, int tid) {
   if (index < 0 || index >= Path.size()) return;
   std::pair<Instruction*, std::string> p = Path[index];
   if (p.first != inst) {
      getSourceMemObjects(index-1, inst, objects, relevantInst, tid);
      return;
   }
   //llvm::errs() << "source for index " << index << " " << (*inst) << "\n";
   if (PathMemObject.find(index) != PathMemObject.end() && 
                      !PathMemObject[index].empty()) {
      for(auto om : PathMemObject[index]) {
         objects.insert(om.second);
         //llvm::errs() << "Adding memobject " << om.second << "\n";
         /*std::pair<Instruction*, std::string> mopinst = Path[index];
         if (mopinst.first->getOpcode() == Instruction::Load)
            recordObjectAction(readMap, om.second, index); 
         else if (mopinst.first->getOpcode() == Instruction::Store)
            recordObjectAction(writeMap, om.second, index);*/
      }
      relevantInst.insert(index);
      return;
   }  
   if (index == 0) return;
   for(unsigned int op=0; op < inst->getNumOperands(); op++) {
      Value *v = inst->getOperand(op);
      if (isa<Instruction>(v)) {
         Instruction *pr = (Instruction*)v;
         getSourceMemObjects(index-1, pr, objects, relevantInst, tid);
      }
   }
}

void ExecutionState::dumpPath() {
  for(unsigned i=0; i<Path.size(); i++) {
     KInstruction *ki = KPath[i];
     const InstructionInfo *tii = ki->info; 
     //llvm::errs() << "Instruction " << i << ":" << tii->file;
     //llvm::errs() << ":" << tii->line; 
     //llvm::errs() << ":" << tii->assemblyLine << "\n"; 
  }
}

void ExecutionState::dumpMemobjects() {
 /* for(auto m : PathMemObject) {
     std::pair<Instruction*,std::string> p = Path[m.first];
     llvm::errs() << "memobjects for " << (*p.first) 
                  << " are:\n" ;
     for(auto mo : m.second) 
        llvm::errs() << mo.second << " ";
     llvm::errs() << "\n"; 
  }
  dumpPath();*/
}

void ExecutionState::dumpStateWithThreads() {
   llvm::errs() << "Main thread:\n";
   if (terminated) 
      llvm::errs() << "terminated.\n";
   else if (!isEnabled(-1)) {
      llvm::errs() << "blocked.\n";
   }
   else {
      llvm::errs() << "active.\n";
   }   
   llvm::errs() << "Stack: \n";
   dumpStack(llvm::errs());
   //dumpPath();
   llvm::errs() << "\n=====================================================\n";
   llvm::errs() << "Thread schedule:\n";
   llvm::errs() << getThreadSchedule() << "\n"; 
   llvm::errs() << "\n=====================================================\n";
   for(unsigned int tid=0; tid<threads.size(); tid++) {
      Async &a = threads[tid];
      llvm::errs() << "Thread " << a.tid << "\n";
      llvm::errs() << "Main function: " << a.function->getName();
      llvm::errs() << "Status: ";
      if (a.terminated) 
         llvm::errs() << "terminated.\n";
      else if (!isEnabled(tid)) {
         llvm::errs() << "blocked.\n";
      }
      else {
         llvm::errs() << "active.\n";
      }   
      KInstruction *tki = a.prevPC;
      const InstructionInfo *tii = tki->info; 
      if (tii->file != "") {
         llvm::errs() << "File: " << tii->file << "\n";
         llvm::errs() << "Line: " << tii->line << "\n";
         llvm::errs() << "assembly.ll line: " << tii->assemblyLine << "\n";
      }
      llvm::errs() << "Stack: \n";
      dumpStackThread(llvm::errs(), tid, false);
      llvm::errs() << "\n=====================================================\n";
  }

}

std::string ExecutionState::getThreadSchedule() {
   createInstThreadMap();
   if (!(instThreadIdMap && instThreadIdMap->size() == Path.size()))
      llvm::errs() << "WARNING: Missing entries in the inst map" 
                   << "possibly due to a timeout\n!";
   //assert(instThreadIdMap && instThreadIdMap->size() == Path.size() && 
   //        "Missing entries in the inst map!\n");
   std::string main = "Main thread";
   std::string schedule = main;
   int current = -1;
   for(unsigned i=0; i<Path.size(); i++) {
      if ((*instThreadIdMap)[i] != current) {
         KInstruction *ki = KPath[i];
         const InstructionInfo *tii = ki->info; 
         current = (*instThreadIdMap)[i];
         if (current == -1)
            schedule += "\n" + main;
         else 
            schedule += "\nThread " + std::to_string(current);
         schedule += ", " + tii->file;
         schedule += ":" + std::to_string(tii->line);
      }
   }
   return schedule;
}

void ExecutionState::createInstThreadMap() {
  if (instThreadIdMap && instThreadIdMap->size() == Path.size()) return;
  instThreadIdMap = new std::map<int, int>();
  for(auto tsp : threadSchedulePoints) {
     llvm::errs() << "Thread segment: [" 
                  << tsp.first << "," << tsp.second.second << "]\n"; 
     for(unsigned i=tsp.first; i<= tsp.second.second; i++) {
        (*instThreadIdMap)[i] = tsp.second.first;
        //llvm::errs() << "Inst id: " << i << " thread id: " 
          //           << (*instThreadIdMap)[i] << "\n";
     }
   }
   if (instThreadIdMap->size() != Path.size()) {
      dumpThreadStates();
      llvm::errs() << "Path size=" << Path.size() 
                   << "Inst map size=" << instThreadIdMap->size() << "\n";
      llvm::errs() << "WARNING: Incomplete map, possibly due to timeout expiration!\n";
   }
   //assert(instThreadIdMap->size() == Path.size());
}

void ExecutionState::recordSharedObjects() {
  if (!sharedObjects.empty()) return;
  std::map<long, std::set<int> > accesses;
  for(int i=0; i<Path.size(); i++) {
     if (PathMemObject.find(i) != PathMemObject.end()) {
        for(auto om : PathMemObject[i])  {
           std::set<int> tids = accesses[om.second];
           tids.insert((*instThreadIdMap)[i]);
           accesses[om.second] = tids;
        }
     }
  } 
  for(auto ae : accesses)
     if (ae.second.size() > 1)
        sharedObjects.insert(ae.first);
}

void ExecutionState::propagateTargetObjectsInstructions(
                                  std::set<long> &objects,
                                  std::set<int> &relevantInst, 
                         std::set<std::pair<Instruction*, std::string> > &IP) {

  createInstThreadMap();
  // find objects/addresses that are accessed by multiple threads 
  recordSharedObjects();
  collectDirectTargetObjectsInstructions(objects, relevantInst, IP);
  llvm::errs() << "Num relevant objects and inst after collect direct: " 
               << "(" << objects.size() << "," << relevantInst.size() << ")\n";
  for(auto lbr : likelyRelevantBranches) {
     if (isLikelyRelevantInstruction(lbr.first, lbr.second)) {
        relevantInst.insert(lbr.first);
        Instruction *inst = dyn_cast<Instruction>(Path[lbr.first].first->getOperand(0)); 
        assert(inst && "branch inst expected!\n");
        llvm::errs() << "relevant branch index " << lbr.first << " " 
                     << (*Path[lbr.first].first) << "\n";
        getSourceMemObjects(lbr.first-1,inst,objects,relevantInst,
                            (*instThreadIdMap)[lbr.first]);
     }
  }
  if (objects.size() == 0) {
     llvm::errs() << "Empty set of property relevant objects\n";
     return;
  }
  std::set<int> newrel = relevantInst;
  bool change = true;
  while(change) 
  {
    std::set<long> newobj1, newobj2;
    std::set<int> newrel1, newrel2;
    // Propagate through the control-flow dependency instructions
    for(auto pr : newrel)
       propagateControlFlow(pr, objects, relevantInst, newobj1, newrel1);
    
    // Propagate through the data-flow dependency
    for(auto pr : newrel)
       propagateDataFlow(pr, objects, relevantInst, newobj2, newrel2);

    change = (newobj1.size() > 0) || (newobj2.size() > 0) || 
             (newrel1.size() > 0) || (newrel2.size()); 

    if (!newobj1.empty()) 
       objects.insert(newobj1.begin(), newobj1.end());
    if (!newobj2.empty()) 
       objects.insert(newobj2.begin(), newobj2.end());
    if (!newrel1.empty())
       relevantInst.insert(newrel1.begin(), newrel1.end());
    if (!newrel2.empty())
       relevantInst.insert(newrel2.begin(), newrel2.end());

    newrel.clear();
    newrel.insert(newrel1.begin(), newrel1.end());
    newrel.insert(newrel2.begin(), newrel2.end());
  }
  llvm::errs() << "Num relevant objects and inst after propagate: " 
               << "(" << objects.size() << "," << relevantInst.size() << ")\n";
  // Now create the read and write maps
  recordObjectActions(objects);
  llvm::errs() << "Num relevant objects and inst after record actions: " 
               << "(" << objects.size() << "," << relevantInst.size() << ")\n";
}

int isAMember(std::pair<Instruction*, std::string> inst, 
     std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
 for(int i=0; i<Part.size(); i++) {
    if (Part[i]->find(inst) != Part[i]->end())
       return i;
 }
 return -1; 
}


// Part will include the partitions
void ExecutionState::computeInterleavingPoints(
                  std::set<std::pair<Instruction*, std::string> > &IP, 
       std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
   llvm::errs() << "Duming path..\n";
   dumpPath();
   std::string sched = getThreadSchedule();
   if (AvoidRedundantDFA) { // Note: Only works for ONE and SINGLETONS modes!!!
      if (IPMap.find(sched) != IPMap.end()) {
         for(auto ip : IPMap[sched])
            IP.insert(ip);
         return;
      }
   }
   std::set<long> objects;
   std::set<int> relevantInst; 
   propagateTargetObjectsInstructions(objects, relevantInst, IP);
   llvm::errs() << "Relevant instructions:\n";
   for(auto i : relevantInst)      
      llvm::errs() << (*Path[i].first) << " " << Path[i].second << "\n";
   llvm::errs() << "Objects: \n";
   for(auto o : objects) {
      llvm::errs() << o << "\n";
   }
   checkHappensBefore(objects, relevantInst, IP, Part);

   if (Part.size() == 0 && IP.size() > 0) {
      std::set<std::pair<Instruction*, std::string> > *ps = 
        new std::set<std::pair<Instruction*, std::string> >();
      for(auto ip : IP)
        ps->insert(ip);
      Part.push_back(ps);
   }

   if (AvoidRedundantDFA)
      IPMap[sched] = IP;
}

bool ExecutionState::threadCreatesThreadHB(int t1, int t2, 
                                           int min, int max) {
  if (min > max) return false;
  long mo2=NULL;
  if (threadIdObjMap.find(t2) != threadIdObjMap.end()) {
     mo2 = threadIdObjMap[t2];
  }
  if (mo2 == NULL) // main thread
     return false;
  for(unsigned i=min; i<max; i++) {
     std::pair<Instruction*, std::string> p = Path[i];
     if ((*instThreadIdMap)[i] == t1) {
        if (p.first->getOpcode() == Instruction::Call || 
            p.first->getOpcode() == Instruction::Invoke) {
           if (threadCreationMap.find(i) != threadCreationMap.end()) {
              if (threadCreationMap[i] == mo2) {
                 return true;
              }
              else { // check for transitive dependency
                int t3 = threadIdMap[(long)threadCreationMap[i]];
                if (threadCreatesThreadHB(t3, t2, i, max))
                   return true;
              }
           }
        }
     }
  }
  return false;
}

bool ExecutionState::threadJoinsThreadHB(int t1, int t2, int min, int max, int i1, int i2) {
  //llvm::errs() << "checking if " << t1 << " joins " << t2 
    //           << " within segment [" << min << "," << max << "]" << "\n";
  if (min > max) return false;
  long mo2 = -2;
  if (threadIdObjMap.find(t2) != threadIdObjMap.end()) {
     mo2 = threadIdObjMap[t2];
     //llvm::errs() << "Mem obj that identifies thread " << t2 
     //             << " is " << mo2 << "\n";	
  }
  if (mo2 == -2) // main thread
     return false;
  //llvm::errs() << "checking if " << t1 << " joins " << t2 << "\n";
  for(int i=max; i>=min; i--) {
     std::pair<Instruction*, std::string> p = Path[i];
     if ((*instThreadIdMap)[i] == t1) {
        if (p.first->getOpcode() == Instruction::Call || 
            p.first->getOpcode() == Instruction::Invoke) {
            //llvm::errs() << "Is join object recorded for thread " 
            //             << t2 << " (thread obj) " 
            //             << mo2 << " at inst no " << i 
            //             << (*Path[i].first) << "\n";
            if (joinObjMap.find(i) != joinObjMap.end()) {  
               //llvm::errs() << mo2 << " vs " << joinObjMap[i] << "?\n";
               if (joinObjMap[i] == mo2) {
                  if (i2 < i) {
                     llvm::errs() << "Thread " << t1 << " joins " << t2 
                               << " at instruction " << i << "\n"; 
                     return true;
                  } 
               }
               else { // transitive case 
                  int t3 = threadIdMap[joinObjMap[i]];
                  if (threadJoinsThreadHB(t3, t2, min, i, i1, i2))
                     return true;
               }
            }
        }
     }
  }
  return false;
}

void ExecutionState::getMatchingRelease(int tid, int index, 
                                        std::set<int> &rels) {
   
   std::pair<Instruction*,std::string> pa = Path[index];
   if (acquireObjMap.find(index) == acquireObjMap.end())
      return;
   long lk = acquireObjMap[index];
   for(int i=index+1; i<Path.size(); i++) 
   {
     std::pair<Instruction*,std::string> p = Path[i];
     int t = (*instThreadIdMap)[i];
     if (t == tid) {
        if (p.first->getOpcode() == Instruction::Call || 
           p.first->getOpcode() == Instruction::Invoke) 
        {
           if (releaseObjMap.find(i) != releaseObjMap.end()) 
           { 
              long lk2 = releaseObjMap[i]; 
              if (lk == lk2) {
                 rels.insert(i);
                 break;
              }
           }
        }
     } 
   }
}

void ExecutionState::getAcquires(int tid, int index, std::set<int> &acqs) {
  std::set<long> relObjs;   
  for(int i=index-1; i >= 0; i--) 
  {
     std::pair<Instruction*,std::string> p = Path[i];
     int t = (*instThreadIdMap)[i];
     if (t == tid) 
     {
        //llvm::errs() << "inst " << i << " executed by thread " 
        //             << tid << "\n";
        //llvm::errs() << (*p.first) << "\n";
        //llvm::errs() << "inst type: " << p.first->getOpcode() << "\n"; 
        if (p.first->getOpcode() == Instruction::Call || 
           p.first->getOpcode() == Instruction::Invoke) 
        {
           //llvm::errs() << "Potential acq/rel at inst " 
           //             << i << " by thread " << tid << "\n";
           if (releaseObjMap.find(i) != releaseObjMap.end()) { 
              relObjs.insert(releaseObjMap[i]); 
              //llvm::errs() << "recorded relase obj " 
              //             << releaseObjMap[i] << "\n";
           }
           else if (acquireObjMap.find(i) != acquireObjMap.end()) {
              //llvm::errs() << "Encountered an acquire obj!\n";
              if (relObjs.find(acquireObjMap[i]) == relObjs.end()) {
                 acqs.insert(i);
                 //llvm::errs() << "recorded acq obj " 
                 //          << acquireObjMap[i] << "\n";
              }
           }
        }
     }
  }
}

void ExecutionState::isInCommonSyncBlocks(int tid1, int i1, int tid2, int i2,
                 std::set<std::pair<int,int> > &common, 
                 std::set<int> &separate,
                 std::set<int> &rels) {
  //llvm::errs() << "Checking for common sync for thread " << tid1 
   //            << " at " << i1 << " and thread " 
   //            << tid2 << " at " << i2 << "\n";

  std::set<int> acq1, acq2;
  getAcquires(tid1, i1, acq1);
  getAcquires(tid2, i2, acq2);
  bool commonFound = false;
  for(auto a1 : acq1) {
     long o1 = acquireObjMap[a1];
     for(auto a2 : acq2) {
        long o2 = acquireObjMap[a2];
        if (o1 == o2) {
           commonFound = true;
           common.insert(std::make_pair(a1,a2));
           getMatchingRelease(tid1, a1, rels);
           getMatchingRelease(tid2, a2, rels);
        }
     }
  }
  if (!commonFound) {
     separate.insert(acq1.begin(), acq1.end());
     separate.insert(acq2.begin(), acq2.end());
     for(auto a1 : acq1) 
        getMatchingRelease(tid1, a1, rels);
     for(auto a2 : acq2) 
        getMatchingRelease(tid2, a2, rels);
  }
}

void ExecutionState::interleavingRelevance(int i1, int i2,
                 std::set<std::pair<int, int> > &ipset, 
                 std::set<int> &separate, std::set<int> &rels) {
  std::pair<Instruction*,std::string> p1 = Path[i1];
  std::pair<Instruction*,std::string> p2 = Path[i2];
  llvm::errs() << "interleaving relevance for " 
               << (*p1.first) << " and " 
               << (*p2.first) << "\n"; 
  int min, max, tmin, tmax;
  if (i1 == i2) 
     return;
  if (i1 < i2) {
     min = i1;
     max = i2;
  }
  else {
     min = i2;
     max = i1;
  }
  tmin = (*instThreadIdMap)[min];
  tmax = (*instThreadIdMap)[max];
  if (tmin == tmax) { 
     llvm::errs() <<  " Performed by the same thread " << tmin << "\n";
     return;
  }
  // check if tmax gets created bw [min,max] and by tmin
  if (threadCreatesThreadHB(tmin, tmax, min, max)) {
     llvm::errs() << "Thread " << tmin <<  " creates " << tmax 
                  << " between " << min << " and " << max << "\n";
     return;
  }
  // check if tmin gets joined by tmax  bw [min,max]
  // since join is a blocking op we need to use 0 for the min 
  // so that the instruction does not get missed!
   
  if (threadJoinsThreadHB(tmax, tmin, 0, max, max, min) || 
      threadJoinsThreadHB(tmin, tmax, 0, max, min, max)) {
     llvm::errs() << "One of the threads join the other (" 
                  <<  tmin << "," << tmax << ") within [0," << max << "\n"; 
     return;
  }
  // check if min and max inside sync blocks using the same object
  std::set<std::pair<int,int> > syncs; 
  llvm::errs() << "Thread " << tmin << " thread " << tmax << "\n";
  isInCommonSyncBlocks(tmin, min, tmax, max, syncs, separate, rels);
  if (syncs.empty()) {
     llvm::errs() << "not in common syncs!\n";
     ipset.insert(std::make_pair(i1,i2));
  }
  else { 
     llvm::errs() << "common sync\n";
     ipset.insert(syncs.begin(), syncs.end());     
  }
}

void printPartitions(std::vector<std::set<std::pair<Instruction*, 
            std::string> > *> &Part);

void sortPartitions(std::vector<std::set<std::pair<Instruction*, 
            std::string> > *> &Part) {
  std::map<unsigned, std::set<int> > objectMap;
  std::vector<int> sizes;  
  for(unsigned i=0; i<Part.size(); i++) {
     std::set<std::pair<Instruction*, 
            std::string> > *is = Part[i];
     sizes.push_back(is->size());
     std::set<int> indices;
     if (objectMap.find(is->size()) != objectMap.end())
        indices = objectMap[is->size()];
     indices.insert(i);
     objectMap[is->size()] = indices;
  }
  std::vector<std::set<std::pair<Instruction*, 
            std::string> > *> temp = Part;
  Part.clear();
  std::sort(sizes.begin(), sizes.end());     
  for(unsigned i=0; i<sizes.size(); i++) {
     std::set<int> indices = objectMap[sizes[i]];
     for(auto index : indices)
        Part.push_back(temp[index]);
  }

}

void updatePartitions(std::set<std::pair<Instruction*,std::string> > &IP,
   std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
   if (IP.size() == 0)
      return; 
   //llvm::errs() << "Partition size before update: " << Part.size() << "\n";
   bool multiple = false;
   std::set<int> pno;
   for(auto ipe : IP) {
      int tpno = isAMember(ipe, Part);
      llvm:errs() << "Is " << ipe.first << " " << (*ipe.first) 
                  << " a member? ";
      if (tpno != -1)  {
         llvm::errs() << "Yes member of partition " << tpno << "\n";
         pno.insert(tpno);
      }
   }
   if (pno.size() == 0) {
      // create a new partition
      std::set<std::pair<Instruction*,std::string> > *np = new 
                std::set<std::pair<Instruction*,std::string> >();
      for(auto ipe : IP) 
         np->insert(ipe);   
      Part.push_back(np);
   }
   else {
      if (pno.size() == 1) { // single partition, place it there
         int no = -1;
         for(auto pnoi : pno)
            no = pnoi;
         for(auto ipe : IP) 
            Part[no]->insert(ipe);
      }
      else { // merge partitions first and then place
         std::vector<std::set<std::pair<Instruction*, std::string> > *> temp; 
         for(unsigned i=0; i<Part.size(); i++)
            temp.push_back(Part[i]);
         Part.clear();
         for(unsigned i=0; i<temp.size(); i++)
            if (pno.find(i) == pno.end())
               Part.push_back(temp[i]);
         std::set<std::pair<Instruction*, std::string> > *np = new 
            std::set<std::pair<Instruction*, std::string> >();
         for(auto ipe : IP)
            np->insert(ipe);
         for(auto pnoi : pno) {
            for(auto pe : (*temp[pnoi]))
               np->insert(pe);
         }
         Part.push_back(np);
      }
   }
   //llvm::errs() << "Partition size after update: " << Part.size() << "\n";
   //printPartitions(Part);
}


void ExecutionState::checkHappensBeforeWW(std::set<long> objects,
                                          std::set<int> relevantInst,
                     std::set<std::pair<Instruction*,std::string> > &IP,  
      std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
   for(auto wrtm : writeMap) {
      std::set<std::pair<Instruction*,std::string> > cIP;
      long obj = wrtm.first;
      llvm::errs() << "Write map for object=" << obj ;
      std::map<int, std::set<int> > wrm = wrtm.second;
      std::set<int> tidw;
      for(auto wr : wrm)  {
         tidw.insert(wr.first);
         llvm::errs() << "\tinst executed by thread " << wr.first << ": "; 
         for(auto wi : wr.second)
            llvm::errs() << "\t\t" << (*Path[wi].first) << "\n";
      }
      if (tidw.size() > 1) {
         for(auto t1 : tidw) {
            for(auto t2 : tidw) {
               if (t1 != t2) {
                  std::set<int> ws1 = wrm[t1];
                  std::set<int> ws2 = wrm[t2];
                  for(auto w1 : ws1) {
                     for(auto w2 : ws2) {
                        std::set<std::pair<int, int> > ps;
                        std::set<int> rels, sep;
                        interleavingRelevance(w1,w2,ps,sep,rels); 
                        for(auto p : ps) {
                           if (p.first >= 0) {
                              IP.insert(Path[p.first]);
                              cIP.insert(Path[p.first]);
                           }
                           if (p.second >= 0) {
                              IP.insert(Path[p.second]);
                              cIP.insert(Path[p.second]);
                           }
                        }
                        for(auto s : sep) {
                           IP.insert(Path[s]);
                           cIP.insert(Path[s]); 
                        }
                        for(auto r : rels) {
                           IP.insert(Path[r]);
                           cIP.insert(Path[r]);
                        }
                     }
                  }
               }
            }
         }
      }
      updatePartitions(cIP, Part);
   }
}

void ExecutionState::checkHappensBeforeWR(std::set<long> objects,
                                          std::set<int> relevantInst,
                       std::set<std::pair<Instruction*,std::string> > &IP,
   std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
   // use WM, RM and hb info to infer the interleaving points
   // find read writes from different threads
   for(auto wrtm : writeMap) {
      std::set<std::pair<Instruction*,std::string> > cIP;
      long obj = wrtm.first;
      std::map<int, std::set<int> > wrm = wrtm.second;
      std::map<int, std::set<int> > rm;
      std::set<int> tidw, tidr;
      for(auto wr : wrm) 
         tidw.insert(wr.first);
      if (readMap.find(obj) != readMap.end()) {
         rm = readMap[obj];
         for(auto r : rm)
            tidr.insert(r.first);                       
      }  
      if (!tidw.empty() && !tidr.empty()) {
         for(auto tw : tidw) {
            for(auto tr : tidr) {
               if (tw != tr) {
                  std::set<int> ws = wrm[tw];
                  std::set<int> rs = rm[tr];
                  for(auto w : ws) {
                     for(auto r: rs) {
                        std::set<std::pair<int, int> > ps;
                        std::set<int> rels, sep; 
                        interleavingRelevance(w,r,ps,sep,rels); 
                        for(auto p : ps) {
                           if (p.first >= 0) {
                              IP.insert(Path[p.first]);
                              cIP.insert(Path[p.first]);
                           }
                           if (p.second >= 0) {
                              IP.insert(Path[p.second]);
                              cIP.insert(Path[p.second]);
                           } 
                        }
                        for(auto s: sep) {
                           IP.insert(Path[s]);
                           cIP.insert(Path[s]);
                        }
                        for(auto r: rels) {
                          IP.insert(Path[r]);
                          cIP.insert(Path[r]);
                        }
                     }
                  }
               }
            }
         }
      }
      updatePartitions(cIP, Part);
   }
}

void printPartitions(std::vector<std::set<std::pair<Instruction*, 
            std::string> > *> &Part) {
   llvm::errs() << "Number of partitions: " << Part.size() << "\n";
   for(unsigned i=0; i<Part.size(); i++) {
      llvm::errs() << "Partition " << i << " size: " << Part[i]->size() << "\n";
      for(auto ipp : (*Part[i]))
         llvm::errs() << "inst=" << (*ipp.first) 
                      << " context= " << ipp.second << "\n";
   } 
}

void ExecutionState::checkHappensBefore(std::set<long> objects,
                                          std::set<int> relevantInst,
                       std::set<std::pair<Instruction*,std::string> > &IP,
     std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part) {
    checkHappensBeforeWR(objects,relevantInst,IP,Part);
    checkHappensBeforeWW(objects,relevantInst,IP,Part);
    printPartitions(Part);
    sortPartitions(Part);
    llvm::errs() << "After sorting the partitions:\n";
    printPartitions(Part);

}

void ExecutionState::branchMT(std::vector<ExecutionState*> &alt, 
                              bool executed) {
   llvm::errs() << "In branchMT, numInterleavings=" << numInterleavings 
                << " maxInterleavings=" << MaxInterleavings << "!\n";
   if (numInterleavings >= MaxInterleavings)
      return;
   numInterleavings++;
   for(unsigned i=0; i<threads.size(); i++) 
   {
      if (i != rtid && !threads[i].terminated && 
          blockedThreads.find(i) == blockedThreads.end()) 
      {
         bool found = false;
         for(auto d : threadsQueue) 
            if (d == i) { found = true; break;}
         llvm::errs()  << "State = " << this  
                       << "alternative schedule thread id " << i << "\n";
         assert(found && "Thread not if threads queue!!!\n");
         ExecutionState *br = this->branch();
         br->rtid = i;
         if (rtid == -1) {
            if (executed)
               br->activeInferenceForExecuted = false;
            else 
               br->activeInferenceForToBeExecuted = false;
         }
         else {
            Async &abr = br->threads[rtid];
            if (executed)
               abr.activeInferenceForExecuted = false;
            else 
               abr.activeInferenceForToBeExecuted = false;
         }
         std::pair<int,int> ti = std::make_pair(rtid, Path.size() - 1);
         if (lastSegmentStartIndex <=  Path.size() - 1)
            // if the previous thread found a chance to execute
            br->threadSchedulePoints[lastSegmentStartIndex] = ti;  
         br->lastSegmentStartIndex = Path.size();
         br->removeFromQueue(i);
         br->addToQueue(rtid);
         alt.push_back(br);
         llvm::errs()  << "State = " << this  << " branches to " << br << "\n";
         dumpThreadStates();
         br->dumpThreadStates();
      }
   }
   if (rtid != -1 && !terminated && 
       blockedThreads.find(-1) == blockedThreads.end()) {
      ExecutionState *br = this->branch();
      br->rtid = -1;
      bool found = false;
      for(auto d : threadsQueue) 
         if (d == -1) { found = true; break;}
      llvm::errs() << "State = " << this 
                   << "alternative schedule thread id " << -1 << "\n";
      dumpThreadStates();
      assert(found && "Thread not if threads queue!!!\n");
      std::pair<int,int> ti = std::make_pair(rtid, Path.size() - 1);
      if (lastSegmentStartIndex <=  Path.size() - 1)
         // if the previous thread found a chance to execute
         br->threadSchedulePoints[lastSegmentStartIndex] = ti;  
      br->lastSegmentStartIndex = Path.size();
      br->removeFromQueue(-1);
      br->addToQueue(rtid);
      assert(rtid != -1);
      Async &abr = br->threads[rtid];
      if (executed)
         abr.activeInferenceForExecuted = false;
      else 
         abr.activeInferenceForToBeExecuted = false; 
      alt.push_back(br);
      llvm::errs()  << "State = " << this  << " branches to " << br << "\n";
      dumpThreadStates();
      br->dumpThreadStates();
   }
   if (alt.size() == 0) {
      numInterleavings--;
      setInterleavingDelayed(true);
   }
}

bool ExecutionState::interleavedAt(std::pair<Instruction*,std::string> p) {
  llvm::errs() << "size of scheduled IP: " << scheduledIP.size() << "\n";
  return (scheduledIP.find(p) != scheduledIP.end());
}

void ExecutionState::recordIPSchedule(std::pair<Instruction*,std::string> p) {
  scheduledIP.insert(p);
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.push_back(StackFrame(caller,kf));
}

/* SYSREL extension */
void ExecutionState::pushFrameThread(KInstIterator caller, KFunction *kf, int tid) {
  threads[tid].stack.push_back(StackFrame(caller,kf));
}
/* SYSREL extension */

void ExecutionState::popFrame() {
  StackFrame &sf = stack.back();
  for (std::vector<const MemoryObject*>::iterator it = sf.allocas.begin(), 
         ie = sf.allocas.end(); it != ie; ++it)
    addressSpace.unbindObject(*it);
  stack.pop_back();
}

/* SYSREL extension */
void ExecutionState::popFrameThread(int tid) {
  StackFrame &sf = threads[tid].stack.back();
  for (std::vector<const MemoryObject*>::iterator it = sf.allocas.begin(), 
         ie = sf.allocas.end(); it != ie; ++it)
    addressSpace.unbindObject(*it);
  threads[tid].stack.pop_back();
}
/* SYSREL extension */

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) { 
  mo->refCount++;
  symbolics.push_back(std::make_pair(mo, array));
}
///

std::string ExecutionState::getFnAlias(std::string fn) {
  std::map < std::string, std::string >::iterator it = fnAliases.find(fn);
  if (it != fnAliases.end())
    return it->second;
  else return "";
}

void ExecutionState::addFnAlias(std::string old_fn, std::string new_fn) {
  fnAliases[old_fn] = new_fn;
}

void ExecutionState::removeFnAlias(std::string fn) {
  fnAliases.erase(fn);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second;
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second;
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?
  if (symbolics!=b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }

  std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  std::set< ref<Expr> > bConstraints(b.constraints.begin(), 
                                     b.constraints.end());
  std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  std::set_intersection(aConstraints.begin(), aConstraints.end(),
                        bConstraints.begin(), bConstraints.end(),
                        std::inserter(commonConstraints, commonConstraints.begin()));
  std::set_difference(aConstraints.begin(), aConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(aSuffix, aSuffix.end()));
  std::set_difference(bConstraints.begin(), bConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(bSuffix, bSuffix.end()));
  if (DebugLogStateMerge) {
    llvm::errs() << "\tconstraint prefix: [";
    for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
                                        ie = commonConstraints.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tA suffix: [";
    for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
                                        ie = aSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tB suffix: [";
    for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
                                        ie = bSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
  }

  // We cannot merge if addresses would resolve differently in the
  // states. This means:
  // 
  // 1. Any objects created since the branch in either object must
  // have been free'd.
  //
  // 2. We cannot have free'd any pre-existing object in one state
  // and not the other

  if (DebugLogStateMerge) {
    llvm::errs() << "\tchecking object states\n";
    llvm::errs() << "A: " << addressSpace.objects << "\n";
    llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  }
    
  std::set<const MemoryObject*> mutated;
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  for (; ai!=ae && bi!=be; ++ai, ++bi) {
    if (ai->first != bi->first) {
      if (DebugLogStateMerge) {
        if (ai->first < bi->first) {
          llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
        } else {
          llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
        }
      }
      return false;
    }
    if (ai->second != bi->second) {
      if (DebugLogStateMerge)
        llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
      mutated.insert(ai->first);
    }
  }
  if (ai!=ae || bi!=be) {
    if (DebugLogStateMerge)
      llvm::errs() << "\t\tmappings differ\n";
    return false;
  }
  
  // merge stack

  ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  for (std::set< ref<Expr> >::iterator it = aSuffix.begin(), 
         ie = aSuffix.end(); it != ie; ++it)
    inA = AndExpr::create(inA, *it);
  for (std::set< ref<Expr> >::iterator it = bSuffix.begin(), 
         ie = bSuffix.end(); it != ie; ++it)
    inB = AndExpr::create(inB, *it);

  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if (av.isNull() || bv.isNull()) {
        // if one is null then by implication (we are at same pc)
        // we cannot reuse this local, so just ignore
      } else {
        av = SelectExpr::create(inA, av, bv);
      }
    }
  }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(), 
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly && 
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      wos->write(i, SelectExpr::create(inA, av, bv));
    }
  }

  constraints = ConstraintManager();
  for (std::set< ref<Expr> >::iterator it = commonConstraints.begin(), 
         ie = commonConstraints.end(); it != ie; ++it)
    constraints.addConstraint(*it);
  constraints.addConstraint(OrExpr::create(inA, inB));

  return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out, bool next) const {
  unsigned idx = 0;
  const KInstruction *target = ((next && pc) ? pc : prevPC);
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }

  /* SYSREL extension */
  for(auto refrec : refCountStack) {
     out << "refcount history of " << refrec.first << "\n";
     for(int i=0; i<refrec.second.size(); i++)
        out << refrec.second[i] << "\n";
  }
  /* SYSREL extension */
}


/* SYSREL */

void ExecutionState::dumpStackCurrentThread(llvm::raw_ostream &out, 
                               KInstruction *ki, bool next) const {
  if (threads[rtid].terminated) return;
  int idx = 0;
  const KInstruction *target;
  if (ki)
     target = ki;
  else  
     target = threads[rtid].prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = threads[rtid].stack.rbegin(), ie = threads[rtid].stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}

void ExecutionState::dumpStackThread(llvm::raw_ostream &out, int tid, bool next) const {
 if (!threads[tid].terminated) {
   out<< "Stack for thread " << tid << "\n";
  unsigned idx = 0;
  KInstruction *target = (next && threads[tid].pc) ? threads[tid].pc : 
                                                     threads[tid].prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = threads[tid].stack.rbegin(), ie = threads[tid].stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
   }
 }
}

void ExecutionState::dumpStackThread(llvm::raw_ostream &out, bool next) const {
  unsigned idx = 0;
  const KInstruction *target = (next && pc) ? pc : prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
  for(unsigned int tid=0; tid<threads.size(); tid++) {
   if (!threads[tid].terminated) {
   out<< "Stack for thread " << tid << "\n";
  idx = 0;
  target = threads[tid].prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = threads[tid].stack.rbegin(), ie = threads[tid].stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (value.get() && isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
 }
 }
}


void ExecutionState::printPC() {
  llvm::outs() << "rtid=" << rtid << "\n";
  if (rtid < 0)
     pc->inst->dump();
  else 
     threads[rtid].pc->inst->dump();
}

bool ExecutionState::allTerminated() {
  if (!terminated) return false;
  for(unsigned i=0; i<threads.size(); i++)
     if (!threads[i].terminated)
        return false;
  return true; 
}

void ExecutionState::completePath(int tid) {
  if (!pathCompleted) {
     std::pair<int,int> ti = std::make_pair(tid, Path.size() - 1);
     threadSchedulePoints[lastSegmentStartIndex] = ti;  
     pathCompleted = true;
  }  
}

void ExecutionState::terminateThread(int tid) {
  llvm::errs() << "State = " << this 
               << "Terminating thread " << tid << "\n";
  
  if ((tid == -1 && terminated) || 
      (tid != -1 && threads[tid].terminated))
     return;

  if (tid == -1) {
     terminated = true;
  }
  std::deque<int> temp;
  while (!threadsQueue.empty()) {  
    int next = threadsQueue.front(); 
    threadsQueue.pop_front();
    if (next != tid)
       temp.push_back(next);  
  }
  threadsQueue = temp;
  if (tid == rtid) {
     std::pair<int,int> ti = std::make_pair(rtid, Path.size() - 1);
     threadSchedulePoints[lastSegmentStartIndex] = ti;  
  }
  if (tid != -1) {
     Async &a = threads[tid]; 
     a.terminated = true;
     a.preemptable = true;
  }
  std::set<int> wtojoint;
  if (threadsBlockedForJoining.find(tid) != threadsBlockedForJoining.end())
     wtojoint = threadsBlockedForJoining[tid];
  std::set<int> es;
  for(auto wt : wtojoint) {
     unblockThread(wt); 
     llvm::errs() << "State = " << this 
                  << "Thread " << tid << " is terminating, unblocking thread "
                  << wt << "\n";
  }
  threadsBlockedForJoining[tid] = es;
}


bool ExecutionState::activeThreads() {
   for(unsigned int i=0; i<threads.size(); i++)
      if (!threads[i].terminated) {
         llvm::errs() << "Thread " << threads[i].tid << " is still active!\n";
         return true;
      }
   return false;
}

bool ExecutionState::threadTerminated(int tid) {
   return threads[tid].terminated;
}

void ExecutionState::setWaitingForThreadsToTerminate(bool value) {
  waitingForThreadsToTerminate = value;
  if (value) {
  // remove the main thread from the scheduler's queue
  llvm::outs() << "queue updated:\n";
  std::deque<int> temp;
  while (!threadsQueue.empty()) {  
    int next = threadsQueue.front(); 
    threadsQueue.pop_front();
    if (next != -1) {
       temp.push_back(next);
       llvm::outs() << next << " ";
    }  
  }
  llvm::outs() << "\n";       
  threadsQueue = temp;
 }
}

bool ExecutionState::getWaitingForThreadsToTerminate() {
  return waitingForThreadsToTerminate;
}

int ExecutionState::getID() {
  return id;
}

void ExecutionState::setLifeCycleModel(Sequential *lcm) {
  LifeCycleModelState::setLifeCycleModel(lcm);
}

bool ExecutionState::hasLCM() {
  return (LifeCycleModelState::lcm != NULL);
}

bool ExecutionState::lcmCompleted() {
  if (hasLCM()) {
    return lcmState->hasCompleted();     
  }
  else return true;
}

int ExecutionState::getLCMState() {
  if (hasLCM()) 
    return lcmState->getCurrentStep();
  return -1;
}

bool ExecutionState::lcmCompletesWith(std::string fn) {
  if (hasLCM()) {
     return lcmState->completesWith(fn);
  }
  else return true;
}

int ExecutionState::getCurrentSuccessReturnValue() {
  if (hasLCM()) 
    return lcmState->getCurrentSuccessValue();
  return 0;
}

BoundAST *ExecutionState::getCurrentSuccessConstraint() {
   if (hasLCM())
      return lcmState->getCurrentSuccessConstraint();
   return NULL;
}


// set up the state according to the next step in the life cycle model
// if move == true then fn is the one that has just returned and 
// completing the current step
// if move == false then fn is the entry point and the current step 
// should be prepared to initialize other components, if any, in the current step
void ExecutionState::updateLCMState() {
  if (lcmState && !lcmState->hasCompleted()) {
     int curr = lcmState->getCurrentStep();
     Sequential *seq = NULL;
     if (curr != 0 || lcmState->isInitialized()) {
        curr++;
        lcmState->moveStep();
     }
     seq  = lcmState->lcm->getStep(curr);            
     if (seq->getType() == parallel) {
           std::vector<std::string> comps = ((Parallel*)seq)->getComponents();
           // Place one as the main thread
           unsigned int entryIndex = comps.size();
           if (curr == 0) {
              // make sure entry function is one of them
             for(unsigned int i=0; i<comps.size(); i++) {
               if (comps[i] == entryFunctionName) {
                  entryIndex = i;
                  break;
               }              
             }
           }
           if (curr == 0 && entryIndex == comps.size()) {
                llvm::outs() << "Invalid life-cycle model: entry function is not part of the first step!\n";
                assert(0);
           }
           else {
             for(unsigned int i=0; i<comps.size(); i++) {
                // create a separate thread for each component
               if (curr != 0 || i != entryIndex) {  
                  Function *func = moduleHandle->getFunction(comps[i]);
                  initiateAsync(func);
               }
             }   
           }
     }
     else if (seq->getType() == identifier) {
       if (curr != 0 ) {
        Identifier *id = dynamic_cast<Identifier*>(seq);
        assert(id);
        llvm::outs() << " next step " << id->getValue() << " to execute " << "\n";
        Function *func = moduleHandle->getFunction(id->getValue());
        //initiateAsync(func); 
        llvm::outs() << "extending current state with " << func->getName() << " to simulate sequential composition\n";
        extendExecutionWith(kmoduleExt->functionMap[func]);
       }
     }
     else assert(0); 
     lcmState->setInitialized();
  }
  llvm::outs() << "LCM state after update: " << lcmState->getCurrentStep() << "\n";
}

bool ExecutionState::lcmStepMovesWhenReturns(std::string fname) {
  return lcmState->stepMovesWhenReturns(fname);
}


Identifier::Identifier(std::string s) {
  name = s;
  type = identifier;
  bast = NULL;
}

BoundAST *Identifier::getSuccessConstraint() {
  return bast;
}

void Identifier::setSuccessConstraint(BoundAST *b) {
  bast = b;
}

void Identifier::setSuccessReturnValue(int value) {
  successretval = value;
}

int Identifier::getSuccessReturnValue() {
  return successretval;
}


void Identifier::print() {
  llvm::outs() << name << " ";
}

std::string Identifier::getValue() { return name; }

Parallel::Parallel(std::vector<std::string> p) {
  par = p;
  type = parallel;
}

int Parallel::getNumInstance(std::string s) {
  int found =0;
  for(unsigned int i=0; i<par.size(); i++)
    if (par[i] == s)
      found++;
  return found;
}

bool Parallel::member(std::string s) {
   for(unsigned int i=0; i<par.size(); i++)
    if (par[i] == s)
      return true;
   return false;
}

std::vector<std::string> Parallel::getComponents() {
  return par;
}

void Parallel::print() {
  llvm::outs() << "( ";
  for(unsigned int i=0; i<par.size(); i++) {
    llvm::outs() << par[i] << " ";
    if (i != par.size() - 1)
      llvm::outs() << "| ";  
  } 
  llvm::outs() << ")";
}


Sequential::Sequential() {
  finalized = false;
  type = sequential;
}

unsigned int Sequential::getNumSteps() {
  return sequence.size();
}

lcmType Sequential::getType() {
  return  type;
}

void Sequential::addStep(Sequential *seq) {
  if (!finalized)
    sequence.push_back(seq);
  else llvm::errs() << "Cannot add step to sequence after finalization!\n";
}

void Sequential::printStep(unsigned int s) {
  if (s < sequence.size())
    sequence[s]->print();
}

void Sequential::print() {
  for(unsigned int i=0; i<sequence.size(); i++) {
    sequence[i]->print();
    if (i != sequence.size() - 1)
       llvm::outs() << "; ";
  }
}

void Sequential::finalize() {
  finalized = true;
}

bool Sequential::isFinalized() {
  return finalized;
}

Sequential *Sequential::getStep(unsigned int i) {
  if (i < sequence.size())
     return sequence[i];
  else return NULL;
}


void LifeCycleModelState::setLifeCycleModel(Sequential *lcmC) {
  lcm = lcmC;
}

Sequential *LifeCycleModelState::getLifeCycleModel() {
  return lcm;
}

LifeCycleModelState::LifeCycleModelState() {
  state = 0;
  initialized = false;
  completed = false;
}

LifeCycleModelState::LifeCycleModelState(LifeCycleModelState &other) {
  state = other.state;
  initialized = other.initialized;
  completed = other.completed;
  componentsCompleted = other.componentsCompleted;
}


bool LifeCycleModelState::moveStep() {
  state++;
  componentsCompleted.clear();
  return (state < lcm->getNumSteps());
}

int LifeCycleModelState::getCurrentStep() {
  return state;
}

int LifeCycleModelState::getCurrentSuccessValue() {
  Sequential *seq = lcm->getStep(state);
  if (seq->getType() == identifier) {
     return ((Identifier*)seq)->getSuccessReturnValue();
  }
  assert(false && "Not sure what to return for concurrent\n!");   
}

BoundAST *LifeCycleModelState::getCurrentSuccessConstraint() {
  Sequential *seq = lcm->getStep(state);
  if (seq->getType() == identifier) 
     return ((Identifier*)seq)->getSuccessConstraint();
  assert(false && "Not sure what to return for concurrent\n!");    
}

bool LifeCycleModelState::hasCompleted() {
  return (state >= lcm->getNumSteps());
}

bool LifeCycleModelState::stepMovesWhenReturns(std::string fname) {
  llvm::outs() << "step moves when " << fname << " returns?\n";
  Sequential *seq = lcm->getStep(state);
  if (seq->getType() == identifier) {
    llvm::outs() << "current state: " << state << "\n";
    llvm::outs() << "current step: " << ((Identifier*)seq)->getValue() << "\n"; 
    return ((Identifier*)seq)->getValue() == fname;
  }
  assert(seq->getType() == parallel);
  std::vector<std::string> comp = ((Parallel*)seq)->getComponents();
  int count = 0;
  for(unsigned int i=0; i<comp.size(); i++) {
    if (comp[i] == fname)
      count++; 
  }
  if (count == 0) return false;
  int countComp = 0;
  for(unsigned int i=0; i<componentsCompleted.size(); i++)
    if (componentsCompleted[i] == fname)
       countComp++;
  return (componentsCompleted.size() == comp.size() - 1) && (countComp == count - 1);
}

bool LifeCycleModelState::isInitialized() {
  return initialized;
}

void LifeCycleModelState::setInitialized() {
  initialized = true;
}

bool LifeCycleModelState::completesWith(std::string fn) {
   llvm::outs() << "checking completes with for " << fn << " state " << state  << "numsteps " << lcm->getNumSteps() << "\n";
   return (state == lcm->getNumSteps() - 1 && stepMovesWhenReturns(fn));
}


AsyncInfo::AsyncInfo(Function *f) {
    function = f;
    count = 1;
    numstarted = 0;  
}

Async::Async(ExecutionState *state, Function *f, int tid,  
             MemoryManager *memory, ref<Expr> arg) {
  function = f;
  KFunction *kf = kmoduleExt->functionMap[f];
  kfunction = kf;  
  pc = kf->instructions;
  prevPC = pc;
  incomingBBIndex = -1;
  preemptable = false; 
  this->tid = tid;
  context = state;
  //stack.push_back(StackFrame(0,kf));
  terminated = false;
  activeInferenceForExecuted = true;
  activeInferenceForToBeExecuted = true; 
  Executor *exe = (Executor*)theInterpreter;
  //context->pushFrameThread(prevPC, kf, tid);
  //if (exe->getStatsTracker())
    // exe->getStatsTracker()->framePushedThread(*context, 0, tid);
  //Cell& ar = stack.back().locals[kf->getArgRegister(0)];
  //ar.value = arg;
  //llvm::errs() << "Thread function arg value: " 
    //           << arg << " stored in register " 
      //         << kf->getArgRegister(0) << "\n";

  /* SYSREL extension */
  /*if (lazyInit) {
   // Lazy init args of the entryFunc
   unsigned int ind = 0;
   for(llvm::Function::arg_iterator ai = f->arg_begin(); ai != f->arg_end(); ai++) {
     Type *at = ai->getType();
     std::string type_str;
     llvm::raw_string_ostream rso(type_str);
     at->print(rso);
     if (at->isPointerTy()) {
        llvm::outs() << "arg " << ind << " type " << rso.str() << "\n";
        at = at->getPointerElementType();
        bool singleInstance = false;
        int count = 0;
        bool lazyInitT = isAllocTypeLazyInit(at, singleInstance, count);
        if (lazyInitT) {
           ref<Expr> laddr;
           llvm::Type *rType;
           bool mksym;
           bool abort = false;
           const MemoryObject *mo = memory->allocateLazyForTypeOrEmbedding(*state, prevPC->inst, at, at, singleInstance, count, rType, laddr, mksym, abort);
           assert(!abort);
           //MemoryObject *mo = memory->allocateForLazyInit(*state, prevPC->inst, at, singleInstance, count, laddr);
           mo->name = state->getUnique(f->getName()) + std::string("arg_") + std::to_string(ind);
           Executor *exe = (Executor*)theInterpreter;
           if (mksym)
              exe->executeMakeSymbolicThread(*state, mo, std::string("arg_") + std::to_string(ind), tid); 
           exe->bindArgumentThread(kf, ind, *state, laddr, tid);
           llvm::outs() << "binding arg " << ind << " of type " << rso.str() << " to address " << laddr << " (in " << mo->getBaseExpr() << ")\n";
        }
     }    
     ind++; 
   }
  }*/
  /* SYSREL extension */


}


// the right context (ExecutionState) must be set separately!
// An example is creating a new ExecutionState through branching
// The same goes for the pc of the thread that is branching
Async::Async(const Async& a) {
  function = a.function;
  kfunction = a.kfunction;  
  pc = a.pc;
  prevPC = a.prevPC;
  incomingBBIndex = a.incomingBBIndex;
  preemptable = a.preemptable; 
  this->tid = a.tid;
  context = a.context;
  stack = a.stack;
  terminated = a.terminated;
  activeInferenceForExecuted = a.activeInferenceForExecuted;
  activeInferenceForToBeExecuted = a.activeInferenceForToBeExecuted;
}

int ExecutionState::initiateAsync(Function *f) { 

  std::string fn = f->getName();
  std::map<std::string, AsyncInfo>::iterator it;
  if ((it = initiatedAsync.find(fn)) != initiatedAsync.end()) {
    // initiated before
    AsyncInfo &aif =  it->second;
    aif.count++;
    return aif.count;
  }
  else {
    AsyncInfo aif(f); 
    initiatedAsync.insert(std::pair<std::string, AsyncInfo>(fn, aif));
    return aif.count;
  }

}

std::string ExecutionState::getCurrentThreadEntryFunctionName() {
  if (rtid >= 0) {
     if (rtid < threads.size() && threads[rtid].function) 
        return threads[rtid].function->getName();
     else return "unknown";
  }
  else return "main";
}

int ExecutionState::createThread(KInstruction *kinst, Function *func, 
                ref<Expr> arg, ref<Expr> metadataId) {
   assert(func && "Thread function not found");
   int id = threads.size();
    ObjectPair op;
    bool success;
    ((Executor*)theInterpreter)->solver->setTimeout(
                       ((Executor*)theInterpreter)->coreSolverTimeout);
    if (!addressSpace.resolveOne(*this, 
            ((Executor*)theInterpreter)->solver, metadataId, op, success)) {
       metadataId = ((Executor*)theInterpreter)->toConstant(*this, metadataId,  
                                    "resolveOne failure");
       success = addressSpace.resolveOne(cast<ConstantExpr>(metadataId), op);
    }
    ref<Expr> result;
    ((Executor*)theInterpreter)->solver->setTimeout(0);
    if (success) {
       const MemoryObject *mo = op.first;
       const ObjectState *os = op.second;
       Expr::Width type = 64/*8*mo->size*/;
       if (mo->size < 8)
          type = 8*mo->size; 
       ref<Expr> offset = mo->getOffsetExpr(metadataId);
       result = ConstantExpr::create(id, type);
       ObjectState *wos = addressSpace.getWriteable(mo, os);
       wos->write(offset, result);
       llvm::errs() << "thread main function: " << func->getName() << "\n";
       llvm::errs() << "wrote thread id to address " << metadataId 
                    << " at offset " << ConstantExpr::create(0,type) 
                    << " of size " << type << "\n";
       llvm::errs() << "pthread create id val: " << result << "\n";
       ref<Expr> rv = wos->read(offset,type);
       llvm::errs() <<  "read value: " << rv << " from address " << metadataId << "\n"; 
    }
    else assert(0 && "Invalid pthread id address\n!"); 
   KFunction *kf = kmoduleExt->functionMap[func];
   Async a(this, func, id, NULL, arg);
   threads.push_back(a);
   pushFrameThread(a.prevPC, kf, id);
   Async &ac = threads[id];
   Cell& ar = ac.stack.back().locals[kf->getArgRegister(0)];
   ar.value = arg;
   llvm::errs() << "Thread function arg value: " 
                << arg << " stored in register " 
                << kf->getArgRegister(0) << "\n";
   if (((Executor*)theInterpreter)->getStatsTracker())
      ((Executor*)theInterpreter)->getStatsTracker()->framePushedThread(*this, 0, id);
   ConstantExpr *CE = dyn_cast<ConstantExpr>(result);
   assert(CE && "Symbolic lock expression not supported");  
   llvm::errs() << "threadIdMap key: " << CE->getZExtValue() << "\n";
   llvm::errs() << "threadIdObjMap key: " << id << "\n";
   threadIdMap[CE->getZExtValue()] = id;
   threadIdObjMap[id] = CE->getZExtValue();
   unsigned rw = ((Executor*)theInterpreter)->getWidthForLLVMType(
                                           kinst->inst->getType());
   if (rtid == -1)
      ((Executor*)theInterpreter)->bindLocal(kinst, *this,  
                                      ConstantExpr::create(0,rw));
   else
      ((Executor*)theInterpreter)->bindLocalThread(kinst, *this,  
                              ConstantExpr::create(0,rw), rtid);

   /*std::pair<Instruction*, std::string> p;
   if (rtid == -1)
      p = std::make_pair(kinst->inst,
                           (Executor*)theInterpreter->getSourceContext());
   else 
      p = std::make_pair(kinst->inst,
                   (Executor*)theInterpreter->getSourceContextThread(tid));*/
   threadCreationMap[Path.size()-1] = CE->getZExtValue();
   addToQueue(id);
   return 0;
}

int ExecutionState::threadJoinsThread(KInstruction *target, 
                                      int idw, int idt) {
  std::set<int> ids;
  long mtid = threadIdObjMap[idt];
  /*std::pair<Instruction*, std::string> p;
  if (tid == -1)
     p = std::make_pair(kinst->inst,
                           (Executor*)theInterpreter->getSourceContext());
  else 
      p = std::make_pair(kinst->inst,
                   (Executor*)theInterpreter->getSourceContextThread(tid));*/
  joinObjMap[Path.size()-1] = mtid;
  dumpThreadStates(); 
  llvm::errs() << "At instruction " << Path.size()-1 
               << idw << " joins object " << mtid << "\n";
  llvm::errs() << "Is joined thread " << idt << "terminated?\n";
  if (threads[idt].terminated) return 0;
  llvm::errs() << "No, thread " << idw << " is going to block!\n";
  if (threadsBlockedForJoining.find(idt) != threadsBlockedForJoining.end())
     ids = threadsBlockedForJoining[idt];
  ids.insert(idw);
  threadsBlockedForJoining[idt] = ids;
  blockThread(idw);
  unsigned rw = ((Executor*)theInterpreter)->getWidthForLLVMType(
                                           target->inst->getType());
   if (rtid == -1)
      ((Executor*)theInterpreter)->bindLocal(target, *this,  
                                      ConstantExpr::create(0,rw));
   else
      ((Executor*)theInterpreter)->bindLocalThread(target, *this,  
                              ConstantExpr::create(0,rw), rtid);
  dumpThreadStates();    
  return 0;
}

int ExecutionState::initLock(KInstruction *kinst, ref<Expr> l) {
  ConstantExpr *CE = dyn_cast<ConstantExpr>(l);
  assert(CE && "Symbolic lock expression not supported");  
  mutexLockMap[CE->getZExtValue()] = true; 
  std::set<int> tids;
  threadsBlockedOnObject[CE->getZExtValue()] =  tids;
  if (rtid == -1)
     ((Executor*)theInterpreter)->bindLocal(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())));
  else if (rtid >= 0) 
     ((Executor*)theInterpreter)->bindLocalThread(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())), rtid);
  return 0;
}

int ExecutionState::lock(KInstruction *kinst, ref<Expr> l) {
  ConstantExpr *CE = dyn_cast<ConstantExpr>(l); 
  assert(CE && "Symbolic lock expression not supported");  
  long la = CE->getZExtValue();
  /*std::pair<Instruction*, std::string> p;
  if (tid == -1)
     p = std::make_pair(kinst->inst,
                           (Executor*)theInterpreter->getSourceContext());
  else 
      p = std::make_pair(kinst->inst,
                   (Executor*)theInterpreter->getSourceContextThread(tid));*/
  acquireObjMap[Path.size()-1] = la;
  if (mutexLockMap.find(la) != mutexLockMap.end()) {
     if (mutexLockMap[la])
        mutexLockMap[la] = false;
     else {
        std::set<int> ids;
        if (threadsBlockedOnObject.find(la) != 
               threadsBlockedOnObject.end()) 
           ids = threadsBlockedOnObject[la];
        ids.insert(rtid);
        threadsBlockedOnObject[la] = ids;
        blockThread(rtid);
        //blockedThreads.insert(rtid);
     }
  } 
  else { // interpret as available (initialized implicitly)
     mutexLockMap[la] = false;
  }
  if (rtid == -1)
     ((Executor*)theInterpreter)->bindLocal(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())));
  else if (rtid >= 0) 
     ((Executor*)theInterpreter)->bindLocalThread(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())), rtid);
  
  return 0;
}

int ExecutionState::unlock(KInstruction *kinst, ref<Expr> l) {
   ConstantExpr *CE = dyn_cast<ConstantExpr>(l); 
   assert(CE && "Symbolic lock expression not supported");  
   long la = CE->getZExtValue();   
   /*std::pair<Instruction*, std::string> p;
   if (tid == -1)
      p = std::make_pair(kinst->inst,
                           (Executor*)theInterpreter->getSourceContext());
   else 
      p = std::make_pair(kinst->inst,
                   (Executor*)theInterpreter->getSourceContextThread(tid));*/
   releaseObjMap[Path.size()-1] = la;

   mutexLockMap[la] = true;
   std::set<int> es;
   if (threadsBlockedOnObject.find(la) != threadsBlockedOnObject.end()) {
      std::set<int> ids = threadsBlockedOnObject[la];
      // unblock only one thread that is not waiting on another object!!!
      unsigned numwoken = 0;
      for(auto bt : ids) {
         if (!waitingOnRelatedToObject(bt, la) && numwoken == 0) {
            unblockThread(bt);
            numwoken++;
         }
         else 
            es.insert(bt);
      }
   }
   threadsBlockedOnObject[la] = es;
  if (rtid == -1)
     ((Executor*)theInterpreter)->bindLocal(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())));
  else if (rtid >= 0) 
     ((Executor*)theInterpreter)->bindLocalThread(kinst, *this, ConstantExpr::create(0,
                  ((Executor*)theInterpreter)->getWidthForLLVMType(kinst->inst->getType())), rtid);
   return 0;
}

int ExecutionState::condInit(KInstruction *kinst, ref<Expr> c) {
   ConstantExpr *CE = dyn_cast<ConstantExpr>(c); 
   assert(CE && "Symbolic condition expression not supported"); 
   long ca = CE->getZExtValue();  
   std::set<int> tids;
   threadsWaitingOnObject[ca] = tids;
   return 0;
}

int ExecutionState::condWait(KInstruction *kinst, ref<Expr> c, ref<Expr> l) {
   ConstantExpr *CE = dyn_cast<ConstantExpr>(c); 
   assert(CE && "Symbolic condition expression not supported");  
   long ca = CE->getZExtValue();  
   CE = dyn_cast<ConstantExpr>(l); 
   assert(CE && "Symbolic lock expression not supported");  
   long la = CE->getZExtValue();  
   std::set<int> cids;
   // make this thread wait on the object
   if (threadsWaitingOnObject.find(ca) != threadsWaitingOnObject.end())
      cids = threadsWaitingOnObject[ca];
   cids.insert(rtid);
   threadsWaitingOnObject[ca] = cids;
   if (threadsReleasingObjectWhileWaitingOnObject.find(ca) != 
          threadsReleasingObjectWhileWaitingOnObject.end()) {
      if (la != threadsReleasingObjectWhileWaitingOnObject[ca])
         assert(0 && "cond var used for different mutex!!!");
   }
   llvm::errs() << "Thread " << rtid << " waiting on cond var " 
                << c << " and releasing lock " << l << "\n";
   threadsReleasingObjectWhileWaitingOnObject[ca] = la;
   // release the lock
   mutexLockMap[la] = true; 
   std::set<int> lids;
  // block this thread on the lock
   if (threadsBlockedOnObject.find(la) != threadsBlockedOnObject.end())
      lids = threadsBlockedOnObject[la];
   lids.insert(rtid);
   threadsBlockedOnObject[la] = lids;
   blockThread(rtid);
   return 0;
}   

bool ExecutionState::waitingOnRelatedToObject(int tid, long la) {
   for(auto wo : threadsReleasingObjectWhileWaitingOnObject) {
      if (wo.second == la) { 
         if (threadsWaitingOnObject.find(wo.first) != 
                 threadsWaitingOnObject.end()) {
            std::set<int> tids = threadsWaitingOnObject[wo.first];
            if (tids.find(tid) != tids.end())
               return true;
         }
      }
   }
   return false;
}

int ExecutionState::condSignalOne(KInstruction *kinst, ref<Expr> c) {
   ConstantExpr *CE = dyn_cast<ConstantExpr>(c); 
   assert(CE && "Symbolic condition expression not supported");  
   long ca = CE->getZExtValue();  
   // remove one thread from the waiting list
   std::set<int> cids;
   int tid = -2;
   llvm::errs() << "Condition variable address: " << ca << "\n";
   for(auto me : threadsWaitingOnObject) {
      llvm::errs() << "Cond var: " << me.first 
                   << " num waiting objects: " << me.second.size() << "\n"; 
   }
   if (threadsWaitingOnObject.find(ca) != threadsWaitingOnObject.end()) {
      std::set<int> cids2;
      cids2 = threadsWaitingOnObject[ca];
      if (cids2.empty()) return 0;
      unsigned num = 0;
      for(auto c2 : cids2) {
         if (num != 0)
            cids.insert(c2);
         else  {
            tid = c2;
            llvm::errs() << "Removing thread " << rtid 
                         << " from the waiting list for " << ca << "\n";
         }
         num++;
      }
      threadsWaitingOnObject[ca] = cids;
   }
   // remember the lock object associated with this object, if any
   if (tid != -2 && threadsReleasingObjectWhileWaitingOnObject.find(ca) != 
          threadsReleasingObjectWhileWaitingOnObject.end()) {
      long la = threadsReleasingObjectWhileWaitingOnObject[ca];
      bool available = false;
      if (mutexLockMap.find(la) != mutexLockMap.end()) 
         available = mutexLockMap[la];
      else  // interpret as available if not accessed via API yet
         available = true;
      if (available) {
         // remove tid from locks 
         std::set<int> lids;
         if (threadsBlockedOnObject.find(la) != threadsBlockedOnObject.end()) {
            for(auto l2 : threadsBlockedOnObject[la]) {
               llvm::errs() << "Thread " << l2 << " blocke on " << la << "\n";
               if (l2 != tid)
                  lids.insert(l2);
               else {
                  // now tid owns it
                  mutexLockMap[la] = false;
                  unblockThread(tid);
                  llvm::errs() << "Thread " <<  tid << " owns mutex " << la << "\n";
               } 
            }
            threadsBlockedOnObject[la] = lids;
         }
      }
   }     
   return 0;
}

int ExecutionState::condSignal(KInstruction *kinst, ref<Expr> c) {
  return condSignalOne(kinst, c);
}

int ExecutionState::condBroadcast(KInstruction *kinst, ref<Expr> c) {
  int result = condSignalOne(kinst, c);   
  ConstantExpr *CE = dyn_cast<ConstantExpr>(c); 
  assert(CE && "Symbolic condition expression not supported");  
  long ca = CE->getZExtValue();  
  std::set<int> cids;
  // empty the waiting list
  threadsWaitingOnObject[ca] = cids;
  return result;
}

bool ExecutionState::isEnabled(int id) {
   if (id == -1 && terminated) return false;
   if (id != -1 && threads[id].terminated)
      return false;
   return (blockedThreads.find(id) == blockedThreads.end());
}

std::set<int> ExecutionState::getEnabled() {
  std::set<int> eset; 
  for(unsigned i=0; i<threads.size(); i++) 
     if (isEnabled(threads[i].tid))
        eset.insert(threads[i].tid);
  return eset;
}

void ExecutionState::dumpThreadStates() {
  llvm::errs() << "Internal state of " << this << "\n"; 
  if (terminated)
     llvm::errs() << "Main thread terminated\n"; 
  else if (!isEnabled(-1))
     llvm::errs() << "Main thread blocked\n"; 
  else { 
     llvm::errs() << "Main thread active\n";
     llvm::errs() << "at " << (*prevPC->inst) << "\n";
  }
  for(unsigned i=0; i<threads.size(); i++) {
     if (threads[i].terminated)
        llvm::errs() << "Thread " << i << " terminated\n";
     else if (!isEnabled(i))
        llvm::errs() << "Thread " << i << " blocked\n";
     else 
        llvm::errs() << "Thread " << i << " active\n";
  }
  llvm::errs() << "Threads in the scheduling queue\n";
  for(auto id : threadsQueue)
     llvm::errs() << id  << " ";
  llvm::errs() << "\n";
     
}

void ExecutionState::addToQueue(int tid) {
  for(auto el : threadsQueue)
     if (el == tid) { 
        llvm::errs() << "Trying to add thread id " << tid << "\n";
        assert(false && "Adding a thread that's already in the queue!");
     }
  threadsQueue.push_back(tid);	 
}

void ExecutionState::removeFromQueue(int tid) {
  std::deque<int>::iterator it = threadsQueue.begin();
  for(;it != threadsQueue.end(); it++)
     if ((*it) == tid)
        break;
  if (it != threadsQueue.end())
     threadsQueue.erase(it);
}

void ExecutionState::blockThread(int tid) {
   blockedThreads.insert(tid);
   removeFromQueue(tid);     
}

void ExecutionState::unblockThread(int tid) {
   std::set<int>::iterator it = blockedThreads.begin();
   for(; it != blockedThreads.end(); it++)
      if (tid == (*it))
         break;
   if (it != blockedThreads.end())
      blockedThreads.erase(it);
   addToQueue(tid); 
}

// return the id of the next thread (main or one of the auxillary threads)
int ExecutionState::scheduleAsync(MemoryManager *memory) {
  llvm::errs() << "State = " << this 
               << "schedule async, current thread " << rtid << "\n";
  dumpThreadStates();
  int prev = rtid;
  std::deque<int>::iterator it = threadsQueue.begin();
  for(;it != threadsQueue.end(); it++) {
     rtid = *it;
     llvm::errs() << "State = " << this  
                  << "Scheduling thread " << rtid << "\n";
     std::pair<int,int> ti = std::make_pair(prev, Path.size() - 1);
     assert(lastSegmentStartIndex <= Path.size() - 1);
     threadSchedulePoints[lastSegmentStartIndex] = ti;  
     lastSegmentStartIndex = Path.size();
     break;
  }
  if (it != threadsQueue.end()) {
     threadsQueue.erase(it);
     if (isEnabled(prev))
        addToQueue(prev);
  }
  if (prev == rtid && !isEnabled(rtid)) {
     llvm::errs()  << "State = " << this 
                   << "Could not find a new thread to schedule!\n";
     dumpThreadStates();
     return -2;
  }
  return rtid;  

/*  if (!waitingForThreadsToTerminate && rtid == -1 && !preemptable) 
    {
    llvm::outs() << "scheduling main again\n";
    return -1;
  }
  if (rtid >= 0 && !threads[rtid].preemptable) 
  {
    llvm::outs() << "scheduling thread " << rtid << " again\n";
    return rtid;
 }
  // Any async to start?
  for(std::map<std::string, AsyncInfo>::iterator it =  initiatedAsync.begin(); 
      it !=  initiatedAsync.end(); it++) {
    if (it->second.numstarted < it->second.count) {
         llvm::outs() << "Starting a new instance for async " << it->second.function->getName() << "\n";
         Async a(this, it->second.function, threads.size(), memory);
         threads.push_back(a); 
         if (threadsQueue.empty())
            threadsQueue.push(-1);
         threadsQueue.push(a.tid);
         Executor *exe = (Executor*)theInterpreter;
         exe->getStatsTracker()->framePushedThread(*this, 0, a.tid);
         it->second.numstarted++;
         rtid = a.tid;
         return a.tid;
     }
  }
  // choose one from the queue !
  if (threadsQueue.empty()) {
     llvm::outs() << "thread queue empty!\n";
     return -1;  // so that main can go ahead and terminate!
  }
  int next = threadsQueue.front(); 
  threadsQueue.pop();
  if (!waitingForThreadsToTerminate || next >= 0)
     threadsQueue.push(next);  
  if (next == -1) {
     llvm::outs() << "scheduling main\n";
     assert(!waitingForThreadsToTerminate);
     preemptable = false;
     rtid = -1;
  }
  else if (next >= 0) {
     llvm::outs() << "scheduling thread " << next << "\n";
     threads[next].preemptable = false;
     rtid = next;
  }
  return next; 
*/
}

int ExecutionState::setPreemptable(int tid, bool value) {
  if (tid == -1) {
     preemptable = value;
     return 0;
  }  
  else if (tid >= 0 && (unsigned int)tid < threads.size()) {
    threads[tid].preemptable = value;
    return 0;
  }
  else return -1;
} 

void ExecutionState::setRefCount(ref<Expr> addr,int value) {
   refCountModel[addr] = value; 
}

int ExecutionState::getRefCount(ref<Expr> addr) {
   if (refCountModel.find(addr) == refCountModel.end())
      refCountModel[addr] = 0;
   return refCountModel[addr];
}

void ExecutionState::setMetadata(ref<Expr> key, ref<Expr> value) {
   metadataMap[key] = value;
   llvm::errs() << "\n metadata " << key << " set to " << value << "\n";
}

ref<Expr> ExecutionState::getMetadata(ref<Expr> key) {
  if (metadataMap.find(key) == metadataMap.end()) {
      metadataMap[key] = ConstantExpr::create(0, 32);
      llvm::errs() << "\n metadata " << key << " added and set to 0\n";
   }
   return metadataMap[key];
}

void ExecutionState::addSymbolDef(std::string sym, ref<Expr> value) {
  symbolDefs[sym] = value;
}
 
ref<Expr> ExecutionState::getSymbolDef(std::string sym) {
  if (symbolDefs.find(sym) != symbolDefs.end())
     return symbolDefs[sym];
  return NULL;
}

void ExecutionState::addSymbolType(std::string sym, llvm::Type *t) {
  symbolTypes[sym] = t;
}
 
llvm::Type *ExecutionState::getSymbolType(std::string sym) {
  if (symbolTypes.find(sym) != symbolTypes.end())
     return symbolTypes[sym];
  return NULL;
}

void ExecutionState::recordAlloc(ref<Expr> address) {
  //llvm::errs() << "Recording alloc " << address << "\n";
  alloced.insert(address);
}

void ExecutionState::recordFree(ref<Expr> address) {
  //llvm::errs() << "Recording free " << address << "\n";
  freed.insert(address);
}

bool ExecutionState::isFreed(ref<Expr> address) {
  return (freed.find(address) != freed.end());
}

void ExecutionState::check() {
   for(auto rfm : refCountModel) {
      if (rfm.second > 0)
         llvm::errs() << "Positive refcount for " << rfm.first << ":" << rfm.second << "\n";
      else if (rfm.second < 0)
         llvm::errs() << "Negative refcount for " << rfm.first << ":" << rfm.second << "\n";
      else 
         llvm::errs() << "Zero refcount for " << rfm.first << ":" << rfm.second << "\n";
   }
 
   llvm::errs() << "Memory leaks:\n";
   for(auto al : alloced) {
      if (freed.find(al) == freed.end())
         llvm::errs() << al << "\n";
   } 
   llvm::errs() << "Memory leaks end:\n";
  
}

void ExecutionState::recordRefcountOp(ref<Expr> addr, std::string record) {
  std::vector<std::string> stack;
  if (refCountStack.find(addr) != refCountStack.end())
     stack = refCountStack[addr];
  stack.push_back(record);
  refCountStack[addr] = stack;
}

std::string ExecutionState::getUnique(std::string n) {
  if (symIdCounters.find(n) == symIdCounters.end()) {
     symIdCounters[n] = 0;
     return n + "_0";
  }
  long int v = symIdCounters[n];
  symIdCounters[n] = v+1;
  return n + "_" + std::to_string(symIdCounters[n]);    
}


PMFrame::PMFrame() {
   action = NULL;
   currentAction = -1;
   target = NULL;
   this->tid = -1;  
   callback = "";
   args.clear();
}

PMFrame::PMFrame(APIAction *a, std::vector< ref<Expr> > &arguments, 
          KInstruction *target, int tid) {
  action = a;
  currentAction = 0;
  this->target = target; 
  for(auto a: arguments)
    args.push_back(a);
  this->tid = tid; 
  callback = "";
}

PMFrame::PMFrame(const PMFrame &pf) {
  action = pf.action;
  currentAction = pf.currentAction;
  target = pf.target; 
  for(auto a: pf.args)
    args.push_back(a);
  tid = pf.tid; 
  callback = pf.callback;
}

void PMFrame::execute(ExecutionState &state, bool &term, bool &comp, bool &abort, ref<Expr> &offendingAddress) {

  llvm::errs() << "PMFrame's action:\n "; action->print();
  action->execute(*this, state, args, target, term, comp, abort, offendingAddress, tid);
  
}

void PMFrame::setCallback(std::string cb) {
  callback = cb;
}

void PMFrame::setPMAction(int cn) {
  currentAction = cn;
}

void ExecutionState::pushPMFrame(APIAction *a, std::vector< ref<Expr> > arguments, 
          KInstruction *target, int tid) {
   PMFrame *pf = new PMFrame(a, arguments, target, tid);
   llvm::errs() << "pushing to PM stack of size=" << pmstack.size() << "\n";
   a->print();
   for(int i=0; i<arguments.size(); i++)
      llvm::errs() << "arg " << i << "=" << arguments[i] << "\n";
   pmstack.push_back(pf);
}

void ExecutionState::popPMFrame() {
   int i;
   if ((i=pmstack.size()) > 0) {
      pmstack.pop_back();
   }
}

// post: either the stack is emptied or the top frame is waiting for a callback to finish
bool ExecutionState::isPMStackEmpty() {
   return (pmstack.size() == 0);
}

void ExecutionState::executePM(bool &abort, ref<Expr> &offendingAddress) {
  if (isPMStackEmpty())
     return;
  int top = pmstack.size() - 1;
  if (pmstack[top]->callback != "") {
     llvm::errs() << "skipping rest of the APIAction to wait for the callback to finish!\n";
     return;
  } 
  llvm::errs() << "Executing PMFrame, callback=" << pmstack[top]->callback << "\n";
  bool term;
  bool comp;
  pmstack[top]->execute(*this, term, comp, abort, offendingAddress);
  if (abort) return;
  if (term || comp) {
     llvm::errs() << "APIAction completed\n"; pmstack[top]->action->print();
     popPMFrame(); 
  }   
  // in case an apisubblock frame is on the stack
  executePM(abort, offendingAddress);
}

void ExecutionState::setPMCallback(std::string cbn) {
  if (isPMStackEmpty())
     assert(false);
  int top = pmstack.size() - 1;
  if (cbn != "" && pmstack[top]->callback != "") {
     llvm::errs() << "callback is already set to " << pmstack[top]->callback << "\n";
     assert(false);
  }
  pmstack[top]->setCallback(cbn);
}

std::string ExecutionState::getPMCallback() {
  if (isPMStackEmpty())
     return "";
  int top = pmstack.size() - 1;
  return pmstack[top]->callback;  
}

void ExecutionState::checkAndSetPMCallbackCompleted(std::string cbn) {
   if (getPMCallback() == cbn) {
      llvm::errs() << "API callback " << cbn << " completed!\n";
      setPMCallback("");
      // Has the APIAction completed?
      if (getPMAction() >= getPMNumActions())
         popPMFrame(); 
   }
}

int ExecutionState::getPMAction() {
    if (isPMStackEmpty())
       return -1;
    int top = pmstack.size() - 1;
    return pmstack[top]->currentAction;
}

int ExecutionState::getPMNumActions() {
    if (isPMStackEmpty())
       return 0;
    int top = pmstack.size() - 1;
    return pmstack[top]->action->getNumActions();
}

std::string reduceWhiteSpace(std::string str) {
   if (str == "") return str;
   // remove all other types of white spaces
   std::string ws = " ";
   std::string otherws = "\t\n\r\f\v";
   size_t pos;
   while ((pos = str.find_first_of(otherws)) != std::string::npos) {
      str = str.replace(pos,1,ws);
   } 
   //now replace sequences of white space with a single white space
   std::string twows = "  ";
   while ((pos = str.find(twows)) != std::string::npos) {
      str = str.replace(pos,2,ws);
   }
   return str;
}



bool matchPattern(std::string constraint, std::string var, bool one) {
    std::string query_1 = "(Eq false (Eq 0 (ReadLSB w32 0 ";
    std::string end_p_1 = ")))";
    std::string query_0 = "(Eq 0 (ReadLSB w32 0 ";
    std::string end_p_0 = "))";
    size_t pos;
    if (one) {
       do {
          pos = constraint.find(query_1);
          if (pos == std::string::npos) return false;
             size_t end = constraint.substr(pos+query_1.length()).find(end_p_1);
          if (end == std::string::npos) return false;
             std::string varcand = constraint.substr(pos+query_1.length(),
                                                     end-(pos+query_1.length())+1);
          if (varcand.find(var) != std::string::npos)
             return true;
          constraint = constraint.substr(end);
       }
       while (pos != std::string::npos);
    }
    else {
      if (matchPattern(constraint, var, true))
         return false;
      do {
          pos = constraint.find(query_0);
          if (pos == std::string::npos) return false;
             size_t end = constraint.substr(pos+query_1.length()).find(end_p_0);
          if (end == std::string::npos) return false;
             std::string varcand = constraint.substr(pos+query_1.length(),
                                                     end-(pos+query_1.length())+1);
          if (varcand.find(var) != std::string::npos)
             return true;
          constraint = constraint.substr(end);
       }
       while (pos != std::string::npos);
      
    }
 
    return false;
} 

bool matchPattern(std::string constraint, std::string var) {
   if (var.find("1_") == 0)
      return matchPattern(constraint, var.substr(2), true);
   else if (var.find("0_") == 0)
      return matchPattern(constraint, var.substr(2), false);
   else assert(0 && "Unexpected pattern in a constraint type attribute\n");
}


double ExecutionState::getCustomWeight() {
    double result = 0.0;

    std::string stackTraceString;
    llvm::raw_string_ostream msg(stackTraceString);
    dumpStack(msg);
    stackTraceString = msg.str();

    std::string pcStr;
    llvm::raw_string_ostream info(pcStr);
    ExprPPrinter::printConstraints(info, constraints);
    pcStr = reduceWhiteSpace(info.str());


    if (ExecutionState::CustomWeightType == "failure") {
       for(auto fp: failureStackTrace)
          if (stackTraceString.find(" "+fp.first+" (") != std::string::npos)
             result += fp.second; 

       for(auto fp: failureConstraint) 
          if (matchPattern(pcStr, fp.first))
             result += fp.second; 
        
    }
    else if (ExecutionState::CustomWeightType == "normal") {
       for(auto fp: normalStackTrace)
          if (stackTraceString.find(" "+fp.first+" (") != std::string::npos)
             result += fp.second; 

       for(auto fp: normalConstraint) 
          if (matchPattern(pcStr, fp.first))
             result += fp.second; 

    }
    else if (ExecutionState::CustomWeightType == "overall") {
       for(auto fp: overallStackTrace)
          if (stackTraceString.find(" "+fp.first+" (") != std::string::npos)
             result += fp.second; 

       for(auto fp: overallConstraint) 
          if (matchPattern(pcStr, fp.first)) {
             result += fp.second;
             llvm::errs() << "matched constraint weight " << result << "\n"; 
          }
    }


    // todo: parse constraint string!!

    llvm::errs() << "custom weight of path " << this << " is " << result;
    llvm::errs() << "stack trace:\n " << stackTraceString << "\n";
    llvm::errs() << "path constraint:\n";
    llvm::errs() << reduceWhiteSpace(pcStr) << "\n";
    return result;
}

// if a subcall returns NULL, it should return NULL 
ref<Expr> rewriteExp(MemoryManager *memman, const MemoryObject *mo, ref<Expr> cexpr, 
                     ref<Expr> offset, ref<Expr> sizep, ref<Expr> nexpr) {
    switch (cexpr->getKind()) {    
      case Expr::Constant: {
        klee::ConstantExpr *CE = dyn_cast<klee::ConstantExpr>(cexpr);
        return klee::ConstantExpr::create(CE->getZExtValue(), CE->getWidth());
      }
      case Expr::Extract: {
        ExtractExpr *EE = dyn_cast<ExtractExpr>(cexpr);
        ref<Expr> eexpr = rewriteExp(memman, mo, cexpr->getKid(0), offset, 
                                     sizep, nexpr);
        if (eexpr.isNull())
           return NULL;
        return ExtractExpr::create(eexpr, EE->offset, EE->width);
      }
      case Expr::Read: {
          ReadExpr *rexpr = dyn_cast<ReadExpr>(cexpr);             
          if (mo->name == rexpr->updates.root->name) {          
             // check offsets and size 
             // if they match, replace
             klee::ConstantExpr *CEI = dyn_cast<klee::ConstantExpr>(rexpr->index);
             klee::ConstantExpr *CEO = dyn_cast<klee::ConstantExpr>(offset);
             klee::ConstantExpr *CES = dyn_cast<klee::ConstantExpr>(sizep);
             if (CEI && CEO && CES && (CEI->getZExtValue() == CEO->getZExtValue())
                 && (CES->getZExtValue() == rexpr->getWidth())) {
                 return nexpr;
             }
             else return NULL; 
             // otherwise return true as a coarse approximation
             // todo : just replace the relevant part for a more precise solution
          }
          else {
             const Array *array = rexpr->updates.root;
             const Array *narray = memman->getArrayCache()->CreateArray(array->name, 
                                                                  array->getSize());
             const UpdateList *rul = new UpdateList(narray,rexpr->updates.head);
             ref<Expr> nrexpr = ReadExpr::alloc(*rul, rexpr->index);     
             //llvm:errs() << "Readexpr: " << cexpr << " renamed as " << nrexpr << "\n";      
             return nrexpr;
          } 
      }  
      case Expr::Concat: {
          ref<Expr> rexpr1 = rewriteExp(memman, mo, cexpr->getKid(0), 
                                        offset, sizep, nexpr);
          if (rexpr1.isNull())
             return NULL; 
          ref<Expr> rexpr2 = rewriteExp(memman, mo, cexpr->getKid(1), 
                                        offset, sizep, nexpr);
          if (rexpr2.isNull())
             return NULL;
          return ConcatExpr::create(rexpr1, rexpr2);
      }
      default:
        std::vector<Expr::CreateArg> args;
        int size = cexpr->getNumKids();
        int i;
        for(i=0; i<size; i++) {
           ref<Expr> rexpr = rewriteExp(memman, mo, cexpr->getKid(i), 
                                        offset, sizep, nexpr);
           if (rexpr.isNull())
              return NULL;
           args.push_back(Expr::CreateArg(rexpr));
           //llvm::errs() << "args[" << i << "] " << args[i].expr << "\n";
        }    
        if (cexpr->getKind() == Expr::SExt || cexpr->getKind() == Expr::ZExt) {
           args.push_back(Expr::CreateArg(cexpr->getWidth()));
           //llvm::errs() << "args[" << i << "] " << args[i].width << "\n";
        }
        //llvm::errs() << "cexpr: " << cexpr << " kind: " << cexpr->getKind() << "\n"; 
        return Expr::createFromKind(cexpr->getKind(), args);
   }
}

/* SYSREL */

