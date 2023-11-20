/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.frontend.ParseContext

open class ProcedurePassManager(val passes: List<ProcedurePass>)

class CPasses(checkOverflow: Boolean, parseContext: ParseContext) : ProcedurePassManager(listOf(
    // formatting
    NormalizePass(parseContext),
    DeterministicPass(parseContext),
    // removing redundant elements
    EmptyEdgeRemovalPass(parseContext),
    UnusedLocRemovalPass(parseContext),
    // optimizing
    SimplifyExprsPass(parseContext),
    // handling intrinsics
    ErrorLocationPass(checkOverflow, parseContext),
    FinalLocationPass(checkOverflow, parseContext),
    SvCompIntrinsicsPass(parseContext),
    FpFunctionsToExprsPass(parseContext),
    PthreadFunctionsPass(parseContext),
    LoopUnrollPass(),
    // trying to inline procedures
    InlineProceduresPass(parseContext),
    RemoveDeadEnds(parseContext),
    EliminateSelfLoops(parseContext),
    // handling remaining function calls
    NondetFunctionPass(parseContext),
    LbePass(parseContext),
    NormalizePass(parseContext), // needed after lbe, TODO
    DeterministicPass(parseContext), // needed after lbe, TODO
    HavocPromotionAndRange(parseContext),
    // Final cleanup
    UnusedVarPass(parseContext),
))

class ChcPasses : ProcedurePassManager(listOf(/*
        // formatting
        NormalizePass(),
        DeterministicPass(),
        // removing redundant elements
        EmptyEdgeRemovalPass(),
        UnusedLocRemovalPass(),
        // optimizing
        SimplifyExprsPass(),
        // handling intrinsics
//        ErrorLocationPass(false),
//        FinalLocationPass(false),
//        SvCompIntrinsicsPass(),
//        FpFunctionsToExprsPass(),
//        PthreadFunctionsPass(),
        // trying to inline procedures
        InlineProceduresPass(),
        RemoveDeadEnds(),
        EliminateSelfLoops(),
        // handling remaining function calls
//        NondetFunctionPass(),
        LbePass(),
        NormalizePass(), // needed after lbe, TODO
        DeterministicPass(), // needed after lbe, TODO
//        HavocPromotionAndRange(),
        // Final cleanup
        UnusedVarPass(),
*/))

class LitmusPasses : ProcedurePassManager(emptyList())