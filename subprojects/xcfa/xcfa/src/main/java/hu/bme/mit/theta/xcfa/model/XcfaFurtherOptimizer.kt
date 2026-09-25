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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

fun XcfaProcedure.deepCopy(
  passManager: ProcedurePassManager,
  unsafeUnrollUsed: Boolean = false,
  identifier: String = "",
): XcfaProcedureBuilder {
  val newLocs = locs.associateWith { it.copy(name = "${it.name}_$identifier") }
  return XcfaProcedureBuilder(
      name = name,
      manager = passManager,
      params = params.toMutableList(),
      vars = vars.toMutableSet(),
      locs = locs.map { newLocs[it]!! }.toMutableSet(),
      edges =
        edges
          .map {
            val source = newLocs[it.source]!!
            val target = newLocs[it.target]!!
            val edge = it.withSource(source).withTarget(target)
            source.outgoingEdges.add(edge)
            target.incomingEdges.add(edge)
            edge
          }
          .toMutableSet(),
      metaData = mutableMapOf(),
      unsafeUnrollUsed = unsafeUnrollUsed,
      prop = prop,
    )
    .also { proc ->
      proc.copyMetaLocs(
        newLocs[initLoc]!!,
        finalLoc.map { newLocs[it] },
        errorLoc.map { newLocs[it] },
      )
    }
}

fun XCFA.optimizeFurther(passManager: ProcedurePassManager): XCFA {
  if (passManager.passes.isEmpty()) return this
  val builder = XcfaBuilder(name, globalVars.toMutableSet())
  procedures.forEach { builder.addProcedure(it.deepCopy(passManager, unsafeUnrollUsed)) }
  initProcedures.forEach { (proc, params) ->
    val initProc =
      builder.getProcedures().find { it.name == proc.name }
        ?: proc.deepCopy(passManager, unsafeUnrollUsed)
    builder.addEntryPoint(initProc, params)
  }
  return builder.build()
}

fun XcfaProcedure.optimizeFurther(
  passManager: ProcedurePassManager,
  name: String? = null,
  identifier: String = "",
): XcfaProcedure {
  val procedureBuilder = deepCopy(passManager, identifier = identifier)
  if (name != null) procedureBuilder.name = name
  val xcfaBuilder = XcfaBuilder(parent.name, parent.globalVars.toMutableSet())
  procedureBuilder.parent = xcfaBuilder
  procedureBuilder.optimize()
  return procedureBuilder.build(parent)
}
