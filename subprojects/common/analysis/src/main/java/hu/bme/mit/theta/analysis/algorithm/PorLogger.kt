/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.core.decl.VarDecl

object PorLogger {
  lateinit var globalVars: Set<VarDecl<*>>
  var precisionableGlobalVarCount: Int? = null
  val exploredActions = mutableListOf<Long>()
  val precGlobalVarSizes = mutableListOf<Int>()
  var virtualExplorationTimeMs: Long = 0
  var dependentTimeMs: Long = 0
  var porTime: Long = 0
  var sporTime: Long = 0

  fun newPrec(prec: Prec) {
    precGlobalVarSizes.add(prec.usedVars.filter { it in globalVars }.size)
  }

  fun printStatistics() {
    System.err.println("POR explored actions (per iteration): $exploredActions")
    System.err.println("Precision global variables (per iteration): $precGlobalVarSizes")
    System.err.println("Number of global variables: $precisionableGlobalVarCount")
    System.err.println("POR algorithm time (ms): ${if (porTime == 0L) sporTime else porTime}")
    System.err.println("SPOR algorithm time (ms): $sporTime")
    System.err.println("DPOR Virtual exploration (ms): $virtualExplorationTimeMs")
    System.err.println("DPOR Dependency calculation time (ms): $dependentTimeMs")
  }
}
