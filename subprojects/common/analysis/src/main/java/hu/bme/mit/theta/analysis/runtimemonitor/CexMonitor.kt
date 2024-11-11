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
package hu.bme.mit.theta.analysis.runtimemonitor

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgTrace
import hu.bme.mit.theta.analysis.runtimemonitor.container.CexHashStorage
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.common.logging.Logger

/**
 * This monitor checks whether a new counterexample is found during the current iteration of CEGAR.
 * In most cases, finding the same counterexample again means that refinement is not progressing.
 * Warning: With some configurations (e.g. lazy pruning) it is NOT impossible that analysis will
 * progress even if in some iterations a new cex is not found, but seems to be rare. However, if you
 * think analysis should NOT be stopped by this monitor, disable it and check results.
 */
class CexMonitor<S : State?, A : Action?>
constructor(private val logger: Logger, private val arg: ARG<S, A>) : Monitor {

  private val cexHashStorage = CexHashStorage<S, A>()
  var lastCex: ArgTrace<S, A>? = null

  fun checkIfNewCexFound(): Boolean {
    return if (arg.cexs.anyMatch { cex -> !cexHashStorage.contains(cex) }) {
      logger.write(Logger.Level.VERBOSE, "Counterexample hash check: new cex found successfully\n")
      true
    } else {
      logger.write(Logger.Level.INFO, "Counterexample hash check: NO new cex found\n")
      false
    }
  }

  fun addNewCounterexample() {
    val newCexs: List<ArgTrace<S, A>> = arg.cexs.filter { !cexHashStorage.contains(it) }.toList()
    assert(newCexs.size == 1, { "Found ${newCexs.size} new cex instead of one" })

    lastCex = newCexs.get(0)
    cexHashStorage.addData(lastCex)
  }

  private fun throwNotSolvable() {
    throw NotSolvableException()
  }

  override fun execute(checkpointName: String) {
    when (checkpointName) {
      "CegarChecker.unsafeARG" ->
        if (checkIfNewCexFound()) addNewCounterexample() else throwNotSolvable()
      else ->
        throw RuntimeException("Unknown checkpoint name in CexMonitor execution: $checkpointName")
    }
  }
}
