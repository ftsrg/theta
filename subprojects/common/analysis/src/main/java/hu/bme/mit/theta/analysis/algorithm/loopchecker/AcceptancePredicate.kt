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
package hu.bme.mit.theta.analysis.algorithm.loopchecker

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import java.util.function.Predicate

class AcceptancePredicate<S : State, A : Action>(
  private val statePredicate: ((S?) -> Boolean)? = null,
  private val actionPredicate: ((A?) -> Boolean)? = null,
) : Predicate<Pair<S?, A?>> {

  constructor(statePredicate: (S?) -> Boolean = { _ -> true }, a: Unit) : this(statePredicate)

  fun testState(state: S): Boolean {
    return statePredicate?.invoke(state) ?: false
  }

  fun testAction(action: A) = actionPredicate?.invoke(action) ?: false

  override fun test(t: Pair<S?, A?>): Boolean {
    val state = t.first
    val action = t.second
    if (statePredicate == null && action == null) return false
    return (statePredicate == null || statePredicate.invoke(state)) &&
      (actionPredicate == null || (action != null && actionPredicate.invoke(action)))
  }
}
