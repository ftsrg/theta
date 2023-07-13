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
package hu.bme.mit.theta.analysis.runtimemonitor.container

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ArgTrace

class CexHashStorage<S : State?, A : Action?> :
    RuntimeDataCollection<ArgTrace<S, A>?> {

    private val counterexamples: MutableSet<Int> = LinkedHashSet()
    override fun addData(newData: ArgTrace<S, A>?) {
        counterexamples.add(newData.hashCode())
    }

    override operator fun contains(data: ArgTrace<S, A>?): Boolean {
        return counterexamples.contains(data.hashCode())
    }
}