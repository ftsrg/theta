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

package hu.bme.mit.theta.xcfa.cli

import com.beust.jcommander.Parameter
import hu.bme.mit.theta.analysis.algorithm.imc.ImcChecker
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaMonolithicTransFunc
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.utils.valToAction
import hu.bme.mit.theta.xcfa.cli.utils.valToState
import hu.bme.mit.theta.xcfa.model.XCFA

data class XcfaImcConfig(
    @Parameter(names = ["--imc-solver"], description = "BMC solver name")
    var imcSolver: String = "Z3",
    @Parameter(names = ["--validate-imc-solver"],
        description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateIMCSolver: Boolean = false,
    @Parameter(names = ["--max-bound"],
        description = "How many successors to enumerate in a transition. Only relevant to the explicit domain. Use 0 for no limit.")
    var maxBound: Int = Int.MAX_VALUE,
    @Parameter
    var remainingFlags: MutableList<String> = ArrayList()
) {

    fun getIMCChecker(xcfa: XCFA, timeout: Int = 0): ImcChecker<XcfaState<ExplState>, XcfaAction> {
        val transFunc = XcfaMonolithicTransFunc.create(xcfa)
        return ImcChecker<XcfaState<ExplState>, XcfaAction>(
            transFunc,
            maxBound,
            getSolver(imcSolver, validateIMCSolver).createItpSolver(),
            { val1 -> valToState(xcfa, val1) },
            { val1, val2 -> valToAction(xcfa, val1, val2) },
            ExprUtils.getVars(transFunc.transExpr),
            timeout)
    }

}