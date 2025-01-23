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

open class ProcedurePassManager(val passes: List<List<ProcedurePass>>) {

  constructor(vararg passes: List<ProcedurePass>) : this(passes.toList())
}

class CPasses(checkOverflow: Boolean, parseContext: ParseContext, uniqueWarningLogger: Logger) :
  ProcedurePassManager(
    listOf(
      // formatting
      NormalizePass(),
      DeterministicPass(),
      // removing redundant elements
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
      // handling intrinsics
      ErrorLocationPass(checkOverflow),
      FinalLocationPass(checkOverflow),
      SvCompIntrinsicsPass(),
      FpFunctionsToExprsPass(parseContext),
      CLibraryFunctionsPass(),
    ),
    listOf(ReferenceElimination(parseContext), MallocFunctionPass(parseContext)),
    listOf(
      // optimizing
      SimplifyExprsPass(parseContext),
      LoopUnrollPass(),
      SimplifyExprsPass(parseContext),
      EmptyEdgeRemovalPass(),
      UnusedLocRemovalPass(),
    ),
    listOf(
      // trying to inline procedures
      InlineProceduresPass(parseContext),
      EmptyEdgeRemovalPass(),
      RemoveDeadEnds(parseContext),
      EliminateSelfLoops(),
    ),
    listOf(StaticCoiPass()),
    listOf(
      // handling remaining function calls
      MemsafetyPass(parseContext),
      NoSideEffectPass(parseContext),
      NondetFunctionPass(),
      LbePass(parseContext),
      NormalizePass(), // needed after lbe, TODO
      DeterministicPass(), // needed after lbe, TODO
      HavocPromotionAndRange(parseContext),
      // Final cleanup
      UnusedVarPass(uniqueWarningLogger),
      EmptyEdgeRemovalPass(),
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
      InlineProceduresPass(parseContext),
      RemoveDeadEnds(parseContext),
      EliminateSelfLoops(),
      // handling remaining function calls
      LbePass(parseContext),
      NormalizePass(), // needed after lbe, TODO
      DeterministicPass(), // needed after lbe, TODO
      // Final cleanup
      UnusedVarPass(uniqueWarningLogger),
    ),
  )

class LitmusPasses : ProcedurePassManager()

class OcExtraPasses :
  ProcedurePassManager(
    listOf(
      AssumeFalseRemovalPass(),
      MutexToVarPass(),
      AtomicReadsOneWritePass(),
      LoopUnrollPass(2), // force loop unroll for BMC
    )
  )
