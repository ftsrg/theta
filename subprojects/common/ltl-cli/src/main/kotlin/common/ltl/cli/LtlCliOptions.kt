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
package hu.bme.mit.theta.common.ltl.cli

import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.enum
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopcheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.ASGTraceCheckerStrategy

open class LtlCliOptions :
  OptionGroup(name = "LTL options", help = "Options related to LTL property checking") {
  val ltlExpression by option(help = "LTL expression to check").required()
  val ltl2BuchiCommand by
    option(
        help =
          "A command that runs on your system. The expression gets appended at the end of it." +
            "For example, if you use SPOT, this should be: `spot ltl2tgba -f`"
      )
      .required()
  val searchStrategy by
    option(help = "Which strategy to use for search")
      .enum<LoopcheckerSearchStrategy>()
      .default(LoopcheckerSearchStrategy.GDFS)
  val refinerStrategy by
    option(help = "Which strategy to use for search")
      .enum<ASGTraceCheckerStrategy>()
      .default(ASGTraceCheckerStrategy.DIRECT_REFINEMENT)
}
