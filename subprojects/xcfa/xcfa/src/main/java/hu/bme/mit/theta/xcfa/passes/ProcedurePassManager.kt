/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.XcfaProperty

open class ProcedurePassManager(val passes: List<List<ProcedurePass>>) {

  constructor(vararg passes: List<ProcedurePass>) : this(passes.toList())

  operator fun plus(other: ProcedurePassManager): ProcedurePassManager =
    ProcedurePassManager(this.passes + other.passes)

  operator fun plus(passes: List<ProcedurePass>): ProcedurePassManager =
    ProcedurePassManager(this.passes + listOf(passes))
}

class CPasses(property: XcfaProperty, parseContext: ParseContext, uniqueWarningLogger: Logger) :
  ProcedurePassManager(
    listOf(
      // formatting
      NormalizePass(),
      DeterministicPass(),
      // removing redundant elements
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
      // handling intrinsics
      ErrorLocationPass(property),
      AssertionToErrorLocationPass(property),
      FinalLocationPass(property),
      SvCompIntrinsicsPass(),
      FpFunctionsToExprsPass(parseContext),
      // must run before CLibraryFunctionsPass reads the handle, and before ReferenceElimination
      // rewrites `&t[i]`
      PthreadArrayHandleUnrollPass(parseContext),
      CLibraryFunctionsPass(parseContext),
      // must run before ReferenceElimination
      AtomicFunctionsPass(parseContext),
    ),
    listOf(
      ReferenceElimination(parseContext),
      // lowers to malloc + memset, so it precedes both
      CallocFunctionPass(parseContext),
      MallocFunctionPass(parseContext),
      AllocaFunctionPass(parseContext),
    ),
    listOf(
      // optimizing
      SimplifyExprsPass(parseContext, property),
      UnrollPass(),
      EmptyEdgeRemovalPass(),
    ),
    listOf(
      // makes indirect calls direct, so that inlining below can see them
      FunctionPointerCallsPass(parseContext, uniqueWarningLogger)
    ),
    listOf(
      // trying to inline procedures
      InlineProceduresPass(parseContext),
      NondetFunctionPass(parseContext),
    ),
    listOf(
      // Clean up procedures after inlining
      InlinedProcedureRemovalPass()
    ),
    listOf(
      // again: inlining turns `&(deref B O)` call arguments into assignments the earlier run of
      // this pass could not see, and no reference may survive into the analyses
      ReferenceElimination(parseContext)
    ),
    listOf(
      // Only now, with the bodies spliced in, is a waiting loop analysable: before inlining its
      // condition is a call, and a call's effect on the caller's variables (its return value above
      // all) is not something the collapse can see. The earlier instance of this pass leaves such a
      // loop alone; this one, which does nothing but collapse busy waits, gets it after inlining.
      UnrollPass(busyWaitsOnly = true, specificRecursionUnrollLimit = -1),
      EmptyEdgeRemovalPass(),
      SimplifyExprsPass(parseContext, property),
      UnusedLocRemovalPass(),
      RemoveDeadEnds(parseContext),
      EliminateSelfLoops(),
    ),
    listOf(StaticCoiPass()),
    listOf(
      // before the memsafety/overflow guards, so those see cells constrained to their C type
      NarrowCellRangePass(parseContext),
      // handling remaining function calls
      MemsafetyPass(property, parseContext),
      NoSideEffectPass(parseContext),
      LbePass(parseContext),
      NormalizePass(), // needed after lbe, TODO
      DeterministicPass(), // needed after lbe, TODO
      EliminateSelfLoops(),
      HavocPromotionAndRange(parseContext),
    ),
    property.witness?.let {
      listOf( // witness
        NormalizePass(), // needed after lbe, TODO
        DeterministicPass(), // needed after lbe, TODO
        EliminateSelfLoops(),
        property.witness.witnessPass(parseContext),
        LbePass(parseContext),
        NormalizePass(), // needed after lbe, TODO
        DeterministicPass(), // needed after lbe, TODO
        SimplifyExprsPass(parseContext, property),
      )
    } ?: emptyList(),
    listOf(DataRaceToReachabilityPass(property, parseContext)),
    listOf(OverflowDetectionPass(property, parseContext)),
    // spells out the mem* copies before anything below havocs the same objects
    listOf(MemoryFunctionsPass(parseContext, uniqueWarningLogger)),
    // last of the passes consuming specific calls: everything left is havoced here
    listOf(
      LibraryStubsPass(parseContext, uniqueWarningLogger),
      UnresolvedInvokeToHavocPass(parseContext, uniqueWarningLogger),
    ),
    // the memory-model passes, downstream of everything that creates or rewrites a dereference
    listOf(FlatMemoryPass(parseContext)),
    listOf(ByteMemoryPass(parseContext)),
    listOf(CloneProcedureForStaticThreadsPass()),
    listOf(InlinedProcedureRemovalPass()),
    listOf(SimplifyExprsPass(parseContext, property)),
    listOf(
      // Final cleanup
      UnusedVarPass(uniqueWarningLogger, property),
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
    ),
  )

class NontermValidationPasses(
  property: XcfaProperty,
  parseContext: ParseContext,
  uniqueWarningLogger: Logger,
) :
  ProcedurePassManager(
    listOf(
      // formatting
      NormalizePass(),
      DeterministicPass(),
      // removing redundant elements
      UnusedLocRemovalPass(),
      // handling intrinsics
      ErrorLocationPass(property),
      AssertionToErrorLocationPass(property),
      FinalLocationPass(property),
      SvCompIntrinsicsPass(),
      FpFunctionsToExprsPass(parseContext),
      // must run before CLibraryFunctionsPass reads the handle, and before ReferenceElimination
      // rewrites `&t[i]`
      PthreadArrayHandleUnrollPass(parseContext),
      CLibraryFunctionsPass(parseContext),
      // must run before ReferenceElimination
      AtomicFunctionsPass(parseContext),
    ),
    listOf(
      ReferenceElimination(parseContext),
      // lowers to malloc + memset, so it precedes both
      CallocFunctionPass(parseContext),
      MallocFunctionPass(parseContext),
      AllocaFunctionPass(parseContext),
    ),
    listOf(
      // optimizing
      UnusedLocRemovalPass()
    ),
    listOf(
      // trying to inline procedures
      InlineProceduresPass(parseContext),
      EliminateSelfLoops(),
    ),
    listOf(
      // handling remaining function calls
      MemsafetyPass(property, parseContext),
      NoSideEffectPass(parseContext),
      NondetFunctionPass(parseContext),
      HavocPromotionAndRange(parseContext),
      // Final cleanup
      UnusedVarPass(uniqueWarningLogger, property),
      UnusedLocRemovalPass(),
    ),
    //        listOf(FetchExecuteWriteback(parseContext)),
  )

class ChcPasses(parseContext: ParseContext, uniqueWarningLogger: Logger) :
  ProcedurePassManager(
    listOf(
      // formatting
      NormalizePass(),
      DeterministicPass(),
      // removing redundant elements
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
      // optimizing
      SimplifyExprsPass(parseContext),
    ),
    listOf(
      // trying to inline procedures
      //      InlineProceduresPass(parseContext),
      RemoveDeadEnds(parseContext),
      //      EliminateSelfLoops(),
      // handling remaining function calls
      //      LbePass(parseContext),
      //      NormalizePass(), // needed after lbe, TODO
      //      DeterministicPass(), // needed after lbe, TODO
      // Final cleanup
      UnusedVarPass(uniqueWarningLogger),
    ),
  )

class LitmusPasses : ProcedurePassManager()

class Btor2Passes(parseContext: ParseContext, uniqueWarningLogger: Logger) :
  ProcedurePassManager(
    listOf(
      LbePass(parseContext),
      NormalizePass(),
      DeterministicPass(),
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
      SimplifyExprsPass(parseContext),
      UnusedVarPass(uniqueWarningLogger),
    )
  )

class Btor2EmptyPass() : ProcedurePassManager() {
  // No optimization
}
