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
package hu.bme.mit.theta.xsts.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.utils.changeVars
import hu.bme.mit.theta.xsts.XSTS

fun XSTS.copyWithReplacingVars(variableMapping: Map<String, VarDecl<*>>): XSTS {
  val matchingCtrlVarNames =
    ctrlVars.filter { variableMapping.containsKey(it.name) }.map { it.name }
  val newCtrlVars =
    ctrlVars.filter { it.name !in variableMapping }.toSet() +
      variableMapping.filter { it.key in matchingCtrlVarNames }.values.toSet()
  return XSTS(
    newCtrlVars,
    init.changeVars(variableMapping) as NonDetStmt,
    tran.changeVars(variableMapping) as NonDetStmt,
    env.changeVars(variableMapping) as NonDetStmt,
    initFormula.changeVars(variableMapping),
    prop.changeVars(variableMapping),
  )
}
