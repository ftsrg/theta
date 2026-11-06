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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

/**
 * Invariants that the liveness-to-safety reduction checks together with its own property.
 * [stateInvariant] must hold in every reachable state. [transitionInvariant] must hold for every
 * reachable state and each earlier state saved by the reduction: each key of [anyPrev] stands for
 * the earlier value of the variable it maps to. States are saved only where [saveCondition] holds,
 * so it must hold on a location of every cycle.
 */
data class LivenessWitness(
  val stateInvariant: Expr<BoolType>,
  val transitionInvariant: Expr<BoolType>,
  val anyPrev: Map<VarDecl<*>, VarDecl<*>>,
  val saveCondition: Expr<BoolType>,
)
