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
      CLibraryFunctionsPass(parseContext),
      // Lowers the __atomic_*/atomic_* builtins into atomic blocks before ReferenceElimination
      // turns their dereferences into the base/offset memory model, like any other `*p`.
      AtomicFunctionsPass(parseContext),
    ),
    listOf(
      ReferenceElimination(parseContext),
      MallocFunctionPass(parseContext),
      ReallocFunctionPass(parseContext),
      AllocaFunctionPass(parseContext),
    ),
    listOf(
      // optimizing
      SimplifyExprsPass(parseContext, property),
      LoopUnrollPass(),
      EmptyEdgeRemovalPass(),
    ),
    listOf(
      // Expand calls through function pointers into a dispatch over their candidate set, so that
      // the direct calls it produces can be inlined below. No-op without indirect calls.
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
      EmptyEdgeRemovalPass(),
      SimplifyExprsPass(parseContext, property),
      UnusedLocRemovalPass(),
      RemoveDeadEnds(parseContext),
      EliminateSelfLoops(),
    ),
    listOf(StaticCoiPass()),
    listOf(
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
        SimplifyExprsPass(parseContext),
      )
    } ?: emptyList(),
    listOf(DataRaceToReachabilityPass(property)),
    listOf(OverflowDetectionPass(property, parseContext)),
    // Spell out the mem* copies before anything havocs them: a havoc would leave the destination
    // holding whatever it held before, which is not what a copy does.
    listOf(MemoryFunctionsPass(parseContext, uniqueWarningLogger)),
    // Havoc remaining calls to unresolved external functions with integer-scalar signatures
    // (all passes that consume specific calls -- free, malloc, pthread_*, nondet -- have
    // already run), so they do not crash the analysis later with "No such method ...".
    listOf(UnresolvedInvokeToHavocPass(parseContext, uniqueWarningLogger)),
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
      CLibraryFunctionsPass(parseContext),
      // Lowers the __atomic_*/atomic_* builtins into atomic blocks before ReferenceElimination
      // turns their dereferences into the base/offset memory model, like any other `*p`.
      AtomicFunctionsPass(parseContext),
    ),
    listOf(
      ReferenceElimination(parseContext),
      MallocFunctionPass(parseContext),
      ReallocFunctionPass(parseContext),
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
