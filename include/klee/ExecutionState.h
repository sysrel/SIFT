//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTIONSTATE_H
#define KLEE_EXECUTIONSTATE_H
/* SYSREL extension */
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include <queue>
#include "../../lib/Core/SpecialFunctionHandler.h"
#include "../../lib/Prose/Prose.h"
/* SYSREL extension */
#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/MergeHandler.h"

// FIXME: We do not want to be exposing these? :(
#include "../../lib/Core/AddressSpace.h"
#include "klee/Internal/Module/KInstIterator.h"


#include <map>
#include <set>
#include <vector>

namespace klee {
class MemoryManager;
class Array;
class CallPathNode;
struct Cell;
struct KFunction;
struct KInstruction;
class MemoryObject;
class PTreeNode;
struct InstructionInfo;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);

class WPState {
  public:
  static unsigned count;
  unsigned id;
  ref<Expr> condition;
  WPState *parent;
  std::vector<long> *children; 
  Instruction *ki;
  long state;
  std::vector<ref<Expr> > *args;
  // store, assume, assert
  std::string *type;
  int numChildrenCompleted;
  const MemoryObject *mo;
  int tid;
  WPState();
};

struct StackFrame {
  KInstIterator caller;
  KFunction *kf;
  CallPathNode *callPathNode;
  int lastCallIndex; 
  std::vector<const MemoryObject *> allocas;
  Cell *locals;

  /// Minimum distance to an uncovered instruction once the function
  /// returns. This is not a good place for this but is used to
  /// quickly compute the context sensitive minimum distance to an
  /// uncovered instruction. This value is updated by the StatsTracker
  /// periodically.
  unsigned minDistToUncoveredOnReturn;

  // For vararg functions: arguments not passed via parameter are
  // stored (packed tightly) in a local (alloca) memory object. This
  // is set up to match the way the front-end generates vaarg code (it
  // does not pass vaarg through as expected). VACopy is lowered inside
  // of intrinsic lowering.
  MemoryObject *varargs;

  StackFrame(KInstIterator caller, KFunction *kf);
  StackFrame(const StackFrame &s);
  ~StackFrame();
};

/* SYSREL extension begin */

struct ConstrainValue {
  enum vtype {INT_TYPE, STRING_TYPE, UNDEF};
  vtype type;
  int ival;
  std::string sval;
};

typedef struct ConstrainValue ConstrainValue_t;

class Async {
public:
  Async(ExecutionState *state, llvm::Function *f, 
        int tid, MemoryManager *memory, ref<Expr> arg);
  Async(const Async&);
  llvm::Function *function;
  KFunction *kfunction;
  std::vector<StackFrame> stack;
  KInstIterator pc;
  KInstIterator prevPC;
  unsigned incomingBBIndex;
  bool preemptable;
  int tid;
  ExecutionState *context;
  bool terminated;
  bool activeInferenceForExecuted;
  bool activeInferenceForToBeExecuted;
  // programming model specific state
  std::map<ref<Expr>,int> stateModel;  
  std::map<ref<Expr>, ref<Expr> > assocModel; 
  std::map<std::string, int> returnValueModel;
};

class AsyncInfo { 
public:
  AsyncInfo(llvm::Function *);
  llvm::Function *function;
  //unsigned blockNo;
  unsigned count;
  unsigned numstarted;
};

enum lcmType { sequential, identifier, parallel};

class Sequential {
private:
  std::vector<Sequential*> sequence;
  bool finalized;
protected:
  lcmType type; 
public:
  Sequential(); 
  void addStep(Sequential *seq);
  void printStep(unsigned int s);
  virtual void print();
  void finalize();
  bool isFinalized();
  unsigned int getNumSteps();
  Sequential *getStep(unsigned int);
  lcmType getType() ;
};



class Identifier : public Sequential {
private:
  std::string name;
  int successretval;
  BoundAST *bast;
public:
  Identifier(std::string s);
  BoundAST *getSuccessConstraint();
  void setSuccessConstraint(BoundAST *);  
  void setSuccessReturnValue(int);
  int getSuccessReturnValue();
  virtual void print();
  std::string getValue();
};

class Parallel : public Sequential {
private:
  std::vector<std::string> par;
public:
  Parallel(std::vector<std::string> p);
  int getNumInstance(std::string s);
  bool member(std::string s);
  std::vector<std::string> getComponents();
  virtual void print(); 
};



class LifeCycleModelState {
private:
  unsigned int state;
  bool initialized;
  bool completed;
  std::vector<std::string> componentsCompleted;
public: 
  static Sequential *lcm;
  static void setLifeCycleModel(Sequential *lcm);
  static Sequential *getLifeCycleModel();
  LifeCycleModelState();
  LifeCycleModelState(LifeCycleModelState&);
  bool moveStep();
  int getCurrentStep();
  int getCurrentSuccessValue();
  BoundAST *getCurrentSuccessConstraint();
  bool hasCompleted();
  bool isInitialized();
  void setInitialized();
  bool stepMovesWhenReturns(std::string);
  bool isCompleted();
  bool completesWith(std::string);
};

class PMFrame {
  private:
   int currentAction;
   APIAction *action;
   KInstruction *target;
   std::vector<ref<Expr> > args;
   int tid;
   std::string callback;
   friend class ExecutionState;
  public:
    PMFrame();
    PMFrame(APIAction *a, std::vector< ref<Expr> > &arguments, 
             KInstruction *target, int tid=-1);
    PMFrame(const PMFrame&);
    void execute(ExecutionState &state, bool &term, bool &comp, bool &abort, ref<Expr> &offendingAddress);
    void setCallback(std::string);
    void setPMAction(int);

};


/* SYSREL extension end */




/// @brief ExecutionState representing a path under exploration
class ExecutionState {
public:
  typedef std::vector<StackFrame> stack_ty;
  /* SYSREL extension begin */
  ref<Expr> lastAccessedAddr;
  const MemoryObject *lastAccessedMem;
  WPState *currentwps; 
  unsigned numInterleavings;
  bool terminated;
  bool cancelled;
  bool activeInferenceForExecuted;
  bool activeInferenceForToBeExecuted;
  std::vector<std::pair<llvm::Value*,ref<Expr> > > lastValuedInst;
  std::string lastContext;
  //std::map<int, KInstruction*> lastkimap;
  const MemoryObject *lastMallocedMem;
  unsigned int stackFrameBeforeExecInst;
  ref<Expr> lastConstraint, lastBranchInstConstraint;
  // Concurrency related fields
  std::set<std::pair<int,int> > likelyRelevantBranches;
  std::map<long, int> threadIdMap;
  std::map<long, bool> mutexLockMap;

  //  these are for mutual exclusion locks
  std::map<long, std::set<int> > threadsBlockedOnObject;
  std::map<int, std::set<int> > threadsBlockedForJoining;
  
  // these are for objects that can be waited on or signaled/broadcast
  std::map<long, std::set<int> > threadsWaitingOnObject;
  // object (cond) waited on -> released object (lock)
  std::map<long, long> threadsReleasingObjectWhileWaitingOnObject;

  // objects that have been accessed by multiple threads
  std::set<long> sharedObjects;
 
  std::set<int> blockedThreads;
  std::map<ref<Expr>,int> lockModel;
  std::map<ref<Expr>,int> stateModel;
  std::map<ref<Expr>, ref<Expr> > assocModel; 
  std::map<std::string, long int> returnValueModel;
  std::map<ref<Expr>, int> refCountModel;
  std::map<ref<Expr>, std::vector<std::string> > refCountStack;
  std::map<ref<Expr>, ref<Expr> > metadataMap; 
  std::map<std::string, ref<Expr> > symbolDefs;
  std::map<std::string, llvm::Type *> symbolTypes;
  std::map<llvm::Type*, ref<Expr> > typeToAddr;
  std::map<ref<Expr>, llvm::Type*> addrToCastFromStructType;
  std::map<std::string, long int> symIdCounters;
  std::vector<PMFrame*> pmstack;
  void pushPMFrame(APIAction *a, std::vector< ref<Expr> > arguments, 
             KInstruction *target, int tid=-1);
  void popPMFrame();
  bool isPMStackEmpty();
  int getPMAction();
  int getPMNumActions();
  void executePM(bool &abort, ref<Expr> &offendingAddress);
  void setPMCallback(std::string cbn);
  std::string getPMCallback();
  void checkAndSetPMCallbackCompleted(std::string cbn);
  bool hasLCM();
  int getLCMState();
  bool lcmCompleted();
  void updateLCMState();
  bool lcmStepMovesWhenReturns(std::string);
  int getCurrentSuccessReturnValue();
  BoundAST *getCurrentSuccessConstraint();
  static void setLifeCycleModel(Sequential *lcm);
  void setWaitingForThreadsToTerminate(bool);
  bool getWaitingForThreadsToTerminate(); 
  void completePath(int tid);
  void terminateThread(int tid);
  bool activeThreads();
  bool allTerminated();
  bool threadTerminated(int tid);
  void printPC();
  int getID();
  bool lcmCompletesWith(std::string);
  void addSymbolDef(std::string, ref<Expr>);
  ref<Expr> getSymbolDef(std::string);
  void addSymbolType(std::string, llvm::Type*);
  void recordRefcountOp(ref<Expr>, std::string);
  void check(); 
  llvm::Type *getSymbolType(std::string);  
  std::map<llvm::Type *, MemoryObject *> lazyInitSingleInstances;
  double getCustomWeight();
  static double CustomWeightThreshold;
  static std::string  CustomWeightType;
  /* SYSREL extension begin */
private:
  // unsupported, use copy constructor
  ExecutionState &operator=(const ExecutionState &);

  std::map<std::string, std::string> fnAliases;
  /* SYSREL extension begin */
  static int counter;
  int id;
  bool waitingForThreadsToTerminate;
  LifeCycleModelState *lcmState;
  std::set<ref<Expr> > alloced;
  std::set<ref<Expr> > freed;
  /* SYSREL extension begin */
public:
  /* SYSREL extension begin */
  // Concurrency related fields
  bool interleavingDelayed; 
  std::map<int, std::map<Instruction*, bool> > interleavingPoints; 
  std::vector<Async> threads;
  // -1 is used for the main thread
  std::deque<int> threadsQueue;
  // running thread id; -1 denotes the main thread
  int rtid; 
  bool pathCompleted;
  // sequence of instructions executed on a path
  std::vector<std::pair<Instruction*, std::string> > Path;
  std::map<unsigned, ref<Expr> > StoreValue;

  std::vector<KInstruction*> KPath;
  // indices are aligned with the indices of Path
  // each element is an operand to memory object map
  // key=-1 for the map is for the return value of the instruction
  //std::map<Instruction*, std::map<std::string, 
  //                       std::map<ref<Expr>, MemoryObject*> > > PathMemObject;
  std::map<int, std::map<ref<Expr>, long> > PathMemObject;
  //std::map<Instruction*, std::map<std::string, 
  //                       std::map<int, ref<Expr> > > > PathValueObject;
  std::map<int, std::map<int, ref<Expr> > > PathValueObject;
  // per instruction versions 
  std::map<ref<Expr>, long> memobjMap;
  std::map<int, ref<Expr> > valueMap;


  //std::map<MemoryObject*, std::map<int, 
  //                        std::pair<Instruction*, std::string> > > readMap;
  std::map<long, std::map<int, std::set<int> > > readMap;
  //std::map<MemoryObject*, std::map<int, 
  //                        std::pair<Instruction*, std::string> > > writeMap;
  std::map<long, std::map<int, std::set<int> > > writeMap;


  std::set<std::pair<Instruction*, std::string> > scheduledIP;
  // first instruction no -> (tid, last inst no in segment)
  std::map<unsigned, std::pair<int,int>> threadSchedulePoints;
  //std::map<std::pair<Instruction*, std::string>, 
  //         MemoryObject*> threadCreationMap;
  std::map<int, long> threadCreationMap;
  std::map<int, long> threadIdObjMap;
  //std::map<std::pair<Instruction*, std::string>, 
  //         MemoryObject*> acquireObjMap;
  std::map<int, long> acquireObjMap;
  //std::map<std::pair<Instruction*, std::string>, 
  //         MemoryObject*> releaseObjMap;
  std::map<int, long> releaseObjMap;
  //std::map<std::pair<Instruction*, std::string>, 
  //         MemoryObject*> joinObjMap;
  std::map<int, long> joinObjMap;
  std::map<int, int> *instThreadIdMap;
  unsigned lastSegmentStartIndex;
  bool preemptable = false; 
  std::map<std::string,AsyncInfo> initiatedAsync;
  std::set<long> globals;

  bool interleavedAt(std::pair<Instruction*,std::string> p);
  void recordIPSchedule(std::pair<Instruction*,std::string> p);
  bool isInterleavingDelayed();
  void setInterleavingDelayed(bool value); 
  std::string getCurrentThreadEntryFunctionName();
  void createInstThreadMap();
  void recordObjectActions(std::set<long> &objects);
  void getSourceMemObjects(int index, Instruction *inst, 
                    std::set<long> &objects, std::set<int> &relevantInst, int tid);  
  bool isRelevantInstruction(Instruction *inst, Function *&calledf);
  bool isLikelyRelevantInstructionDepth(BasicBlock *bb, 
                                         std::set<BasicBlock*> &visited, int depth) ;
  bool isLikelyRelevantInstruction(int index, int br);
  void updateLikelyRelevantBranches(int index, int br);
  void addToQueue(int tid);
  void removeFromQueue(int tid); 
  void blockThread(int tid);
  void unblockThread(int tid);
  bool isEnabled(int id);
  std::set<int> getEnabled();
  int createThread(KInstruction *kinst, Function *func, ref<Expr> arg, 
                   ref<Expr> tidobj);
  int threadJoinsThread(KInstruction *target, int idw, int idt); 
  int initLock(KInstruction *target, ref<Expr>);
  int lock(KInstruction *target, ref<Expr>);
  int unlock(KInstruction *target, ref<Expr>);

  int condInit(KInstruction *kinst, ref<Expr> c);
  int condWait(KInstruction *kinst, ref<Expr> c, ref<Expr> l);
  bool waitingOnRelatedToObject(int tid, long la);
  int condSignalOne(KInstruction *kinst, ref<Expr> c);  
  int condSignal(KInstruction *kinst, ref<Expr> c);
  int condBroadcast(KInstruction *kinst, ref<Expr> c);

  void dumpMemobjects();
  void dumpStateWithThreads();
  void dumpPath();
  void dumpThreadStates();
  std::string getThreadSchedule();

  bool storedInGlobal(long mo, int min, int max) ;

  bool addressFlowsInto(long smo, long dmo, int min, int max);

  bool flowsIntoThreadCreate(long mo, int min, int max);

  bool localAddressEscapes(long mo, int max);

  void matchReturnGetOperands(ref<Expr> retVal, 
                                            std::set<ref<Expr> > &ops);
  void getValues(int index, std::set<Instruction*> &values, 
                 unsigned minoperand, bool returnVal);

  

  bool getMemObjects(ref<Expr> value, 
                     std::set<long> &objects,
                     std::set<int> &relevantInst);
  
  void getMemObjectsAll(ref<Expr> value, 
                        std::set<long> &objects,
                        std::set<int> &relevantInst);

  void processGep(int index, 
                  std::set<long> &objects,
                  std::set<int> &relevantInst);

  void processTargetCall(int index, 
                                 std::set<long> &objects,
                                 std::set<int> &relevantInst,
                                 std::set<std::pair<Instruction*,
                                                    std::string> > &IP, 
                                 bool args, bool ret);

  void processCall(int index, 
                   std::set<long> &objects,
                   std::set<int> &relevantInst, 
                   std::string name, bool args, bool ret);

  void processMallocs(int max, 
                      std::set<long> &objects,
                      std::set<int> &relevantInst);

  void recordObjectAction(std::map<long, 
                          std::map<int, std::set<int> > > &rwmap,
                          long obj, int index);

  void processNonLocalPointerAccess(int index, 
                         std::set<long> &objects,
                         std::set<int> &relevantInst);

  void processLoadFromHeap(int index, 
                           std::set<long> &objects,
                           std::set<int> &relevantInst); 

  void collectDirectTargetObjectsInstructions(
                                  std::set<long> &objects,
                                  std::set<int> &relevantInst, 
                                  std::set<std::pair<Instruction*,
                                                    std::string> > &IP);

  void collectPrecedingBranches(int index, int tid, std::set<int> &br);


  int getThreadIdForIndex(int index);

  void propagateControlFlow(int index,
                            std::set<long> &objects,
                            std::set<int> &relevantInst, 
                            std::set<long> &nobjects,
                            std::set<int> &nrelevantInst);

  long getMemoryObjectForLoadStore(int index);

  bool collectMostRecentWrite(int index, int tid, int &write);

  void propagateDataFlow(int index,
                         std::set<long> &objects,
                         std::set<int> &relevantInst, 
                         std::set<long> &nobjects,
                         std::set<int> &nrelevantInst);
 
  void propagateTargetObjectsInstructions(std::set<long> &objects,
                                          std::set<int> &relevantInst, 
                                          std::set<std::pair<Instruction*,
                                                    std::string> > &IP);
  
  std::map<std::string, std::set<std::pair<Instruction*,
                                           std::string> > > IPMap;

  void recordSharedObjects();

  void computeInterleavingPoints(std::set<std::pair<Instruction*,
                                                    std::string> > &IP, 
      std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part);

  bool threadCreatesThreadHB(int t1, int t2, int min, int max);

  bool threadJoinsThreadHB(int t1, int t2, int min, int max, int t1pos, int t2pos);

  void getAcquires(int tid, int index, std::set<int> &acqs);
 
  void getMatchingRelease(int tid, int index, std::set<int> &rels);

  void isInCommonSyncBlocks(int tid1, int i1, int tid2, int i2,
                            std::set<std::pair<int,int> > &common,
                            std::set<int> &separate, std::set<int> &rels);

  void interleavingRelevance(int i1, int i2,
                             std::set<std::pair<int, int> > &ipset, 
                             std::set<int> &separate, std::set<int> &rels);

  void checkHappensBeforeWW(std::set<long> objects,
                            std::set<int> relevantInst,
                       std::set<std::pair<Instruction*,std::string> > &IP, 
      std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part);


  void checkHappensBeforeWR(std::set<long> objects,
                            std::set<int> relevantInst,
                       std::set<std::pair<Instruction*,std::string> > &IP, 
      std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part);

  void checkHappensBefore(std::set<long> objects,
                          std::set<int> relevantInst,
                       std::set<std::pair<Instruction*,std::string> > &IP, 
      std::vector<std::set<std::pair<Instruction*, std::string> > *> &Part);


  bool happensBefore(std::pair<Instruction*, std::string> i1,
                     std::pair<Instruction*, std::string> i2);

  int initiateAsync(llvm::Function *f);
  int scheduleAsync(MemoryManager *memory);
  int setPreemptable(int tid, bool value);
  void setRefCount(ref<Expr>,int); 
  int getRefCount(ref<Expr>); 
  void setMetadata(ref<Expr>, ref<Expr>);
  ref<Expr> getMetadata(ref<Expr>);
  std::string getUnique(std::string);
  /* SYSREL extension end */
  // Execution - Control Flow specific

  /// @brief Pointer to instruction to be executed after the current
  /// instruction
  KInstIterator pc;

  /// @brief Pointer to instruction which is currently executed
  KInstIterator prevPC;

  /// @brief Stack representing the current instruction stream
  stack_ty stack;

  /// @brief Remember from which Basic Block control flow arrived
  /// (i.e. to select the right phi values)
  unsigned incomingBBIndex;

  // Overall state of the state - Data specific

  /// @brief Address space used by this state (e.g. Global and Heap)
  AddressSpace addressSpace;

  /// @brief Constraints collected so far
  ConstraintManager constraints;

  /// Statistics and information

  /// @brief Costs for all queries issued for this state, in seconds
  mutable double queryCost;

  /// @brief Weight assigned for importance of this state.  Can be
  /// used for searchers to decide what paths to explore
  double weight;

  /// @brief Exploration depth, i.e., number of times KLEE branched for this state
  unsigned depth;

  /// @brief History of complete path: represents branches taken to
  /// reach/create this state (both concrete and symbolic)
  TreeOStream pathOS;

  /// @brief History of symbolic path: represents symbolic branches
  /// taken to reach/create this state
  TreeOStream symPathOS;

  /// @brief Counts how many instructions were executed since the last new
  /// instruction was covered.
  unsigned instsSinceCovNew;

  /// @brief Whether a new instruction was covered in this state
  bool coveredNew;

  /// @brief Disables forking for this state. Set by user code
  bool forkDisabled;

  /// @brief Set containing which lines in which files are covered by this state
  std::map<const std::string *, std::set<unsigned> > coveredLines;

  /// @brief Pointer to the process tree of the current state
  PTreeNode *ptreeNode;

  /// @brief Ordered list of symbolics: used to generate test cases.
  //
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<const MemoryObject *, const Array *> > symbolics;

  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames;

  std::string getFnAlias(std::string fn);
  void addFnAlias(std::string old_fn, std::string new_fn);
  void removeFnAlias(std::string fn);

  // The objects handling the klee_open_merge calls this state ran through
  std::vector<ref<MergeHandler> > openMergeStack;

  // The numbers of times this state has run through Executor::stepInstruction
  std::uint64_t steppedInstructions;

private:
  ExecutionState() : ptreeNode(0) {}

public:
  ExecutionState(KFunction *kf);

  // XXX total hack, just used to make a state so solver can
  // use on structure
  ExecutionState(const std::vector<ref<Expr> > &assumptions);

  ExecutionState(const ExecutionState &state);

  /* SYSREL EXTENSION */
  // continue a path after termination with a new function executed sequentially
  void extendExecutionWith(KFunction *kf);
  /* SYSREL EXTENSION */
  

  ~ExecutionState();


  ExecutionState *branch();

  void branchMT(std::vector<ExecutionState*> &alt, bool executed);

  void pushFrame(KInstIterator caller, KFunction *kf);
  /* SYSREL extension */
  void pushFrameThread(KInstIterator caller, KFunction *kf, int tid);
  /* SYSREL extension */
  void popFrame();
  /* SYSREL extension */
  void popFrameThread(int tid);
  /* SYSREL extension */

  void addSymbolic(const MemoryObject *mo, const Array *array);
  void addConstraint(ref<Expr> e) { constraints.addConstraint(e); }

  bool merge(const ExecutionState &b);
  void dumpStack(llvm::raw_ostream &out, bool next=false) const;
  /* SYSREL extension */
  void dumpStackCurrentThread(llvm::raw_ostream &out, KInstruction *ki=NULL, 
                              bool next=false) const;
  void dumpStackThread(llvm::raw_ostream &out, bool next=false) const;
  void dumpStackThread(llvm::raw_ostream &out, int tid, bool next=false) const;
  void recordAlloc(ref<Expr>);
  void recordFree(ref<Expr>);
  bool isFreed(ref<Expr>); 
  /* SYSREL extension */
};

}
// makes a copy of orig
// replaces any read expr involving mo->name in orig and returns the new expr
//  if offset is not a perfect match in orig, approximates it by returning true
// todo: may as well just replace the relevant part with a true
ref<Expr> rewriteExp(MemoryManager *memory, const MemoryObject *mo, ref<Expr> cexpr, 
                     ref<Expr> offset, ref<Expr> sizep, ref<Expr> nexpr);



#endif
