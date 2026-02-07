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

package hu.bme.mit.theta.analysis.algorithm.refinery

import tools.refinery.logic.dnf.RelationalQuery
import tools.refinery.store.dse.transition.Rule

class RefineryTransitionSystem(
  val textualDeclarations: String,
  val transitions: List<ProblemContext.() -> Rule>,
  val target: ProblemContext.() -> RelationalQuery,
)
