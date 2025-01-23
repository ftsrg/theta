/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace

/** Traces built on ArgTraces, but capable of handling traces going through covered nodes */
class PatchArgTrace<S : State, A : Action> private constructor(val traces: List<ArgTrace<S, A>>) :
  Iterable<ArgNode<S, A>?> {
  private val nodes: List<ArgNode<S, A>> = traces.flatten()

  override fun iterator(): Iterator<ArgNode<S, A>?> {
    return nodes.iterator()
  }

  companion object {
    fun <S : State, A : Action> create(traces: List<ArgTrace<S, A>>): PatchArgTrace<S, A> {

      return PatchArgTrace<S, A>(traces)
    }
  }
}
