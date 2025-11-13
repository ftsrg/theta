/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
      FinalLocationPass(property),
      SvCompIntrinsicsPass(),
      FpFunctionsToExprsPass(parseContext),
    ),
    listOf(ReferenceElimination(parseContext), MallocFunctionPass(parseContext)),
    listOf(
      // optimizing
      LoopUnrollPass(),
      SimplifyExprsPass(parseContext, property),
      LoopUnrollPass(),
      EmptyEdgeRemovalPass(),
      ReferenceDereferenceSimplifier(parseContext),
    ),
    listOf(
      // trying to inline procedures, but transform C library functions first
      CLibraryFunctionsPass(),
      InlineProceduresPass(parseContext),
      NondetFunctionPass(),
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
      FinalLocationPass(property),
      SvCompIntrinsicsPass(),
      FpFunctionsToExprsPass(parseContext),
      CLibraryFunctionsPass(),
    ),
    listOf(ReferenceElimination(parseContext), MallocFunctionPass(parseContext)),
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
      NondetFunctionPass(),
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
