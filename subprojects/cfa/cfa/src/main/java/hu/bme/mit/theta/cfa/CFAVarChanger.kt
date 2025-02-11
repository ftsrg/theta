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
package hu.bme.mit.theta.cfa

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.changeVars

/**
 * Extension function for CFA. Creates a new CFA which looks exactly the same, but any variable
 * whose name is present in the parameter gets replaced to the associated instance.
 */
fun CFA.copyWithReplacingVars(variableMapping: Map<String, VarDecl<*>>): CFA {
  val builder = CFA.builder()
  val locationMap: Map<String, CFA.Loc> = locs.associate { it.name to builder.createLoc(it.name) }
  builder.initLoc = locationMap[initLoc.name]
  if (errorLoc.isPresent) builder.errorLoc = locationMap[errorLoc.get().name]
  if (finalLoc.isPresent) builder.finalLoc = locationMap[finalLoc.get().name]
  edges.forEach {
    builder.createEdge(
      locationMap[it.source.name],
      locationMap[it.target.name],
      it.stmt.changeVars(variableMapping),
    )
  }
  return builder.build()
}
