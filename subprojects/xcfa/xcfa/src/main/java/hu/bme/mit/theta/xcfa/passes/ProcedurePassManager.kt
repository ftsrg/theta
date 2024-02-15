/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

open class ProcedurePassManager(vararg passes: List<ProcedurePass>) {

    val passes: List<List<ProcedurePass>> = passes.toList()
}

class CPasses(checkOverflow: Boolean, parseContext: ParseContext, uniqueWarningLogger: Logger) : ProcedurePassManager(
    listOf(
        // formatting
        NormalizePass(parseContext),
        DeterministicPass(parseContext),
        // removing redundant elements
        EmptyEdgeRemovalPass(parseContext),
        UnusedLocRemovalPass(parseContext),
        // handling intrinsics
        ErrorLocationPass(checkOverflow, parseContext),
        FinalLocationPass(checkOverflow, parseContext),
        SvCompIntrinsicsPass(parseContext),
        FpFunctionsToExprsPass(parseContext),
        CLibraryFunctionsPass(parseContext),
    ),
    listOf(
        // optimizing
        SimplifyExprsPass(parseContext),
        LoopUnrollPass(),
    ),
    listOf(
        // trying to inline procedures
        InlineProceduresPass(parseContext),
        RemoveDeadEnds(parseContext),
        EliminateSelfLoops(parseContext),
    ),
    listOf(
        // handling remaining function calls
        NondetFunctionPass(parseContext),
        LbePass(parseContext),
        NormalizePass(parseContext), // needed after lbe, TODO
        DeterministicPass(parseContext), // needed after lbe, TODO
        HavocPromotionAndRange(parseContext),
        // Final cleanup
        UnusedVarPass(parseContext, uniqueWarningLogger),
    )
)

class ChcPasses(parseContext: ParseContext, uniqueWarningLogger: Logger) : ProcedurePassManager(listOf(
    // formatting
    NormalizePass(parseContext),
    DeterministicPass(parseContext),
    // removing redundant elements
    EmptyEdgeRemovalPass(parseContext),
    UnusedLocRemovalPass(parseContext),
    // optimizing
    SimplifyExprsPass(parseContext),
    // handling intrinsics
//        ErrorLocationPass(false),
//        FinalLocationPass(false),
//        SvCompIntrinsicsPass(),
//        FpFunctionsToExprsPass(),
//        PthreadFunctionsPass(),
    // trying to inline procedures
), listOf(
    InlineProceduresPass(parseContext),
    RemoveDeadEnds(parseContext),
    EliminateSelfLoops(parseContext),
    // handling remaining function calls
//        NondetFunctionPass(),
    LbePass(parseContext),
    NormalizePass(parseContext), // needed after lbe, TODO
    DeterministicPass(parseContext), // needed after lbe, TODO
//        HavocPromotionAndRange(),
    // Final cleanup
    UnusedVarPass(parseContext, uniqueWarningLogger),
))

class LitmusPasses : ProcedurePassManager()