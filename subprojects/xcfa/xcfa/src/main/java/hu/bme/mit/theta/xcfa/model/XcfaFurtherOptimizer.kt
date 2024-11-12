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
package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

fun XCFA.optimizeFurther(passes: List<ProcedurePass>): XCFA {
  if (passes.isEmpty()) return this
  val passManager = ProcedurePassManager(passes)
  val copy: XcfaProcedureBuilder.() -> XcfaProcedureBuilder = {
    val newLocs = getLocs().associateWith { it.copy() }
    XcfaProcedureBuilder(
        name = name,
        manager = passManager,
        params = getParams().toMutableList(),
        vars = getVars().toMutableSet(),
        locs = getLocs().map { newLocs[it]!! }.toMutableSet(),
        edges =
          getEdges()
            .map {
              val source = newLocs[it.source]!!
              val target = newLocs[it.target]!!
              val edge = it.withSource(source).withTarget(target)
              source.outgoingEdges.add(edge)
              target.incomingEdges.add(edge)
              edge
            }
            .toMutableSet(),
        metaData = metaData.toMutableMap(),
      )
      .also {
        it.copyMetaLocs(
          newLocs[initLoc]!!,
          finalLoc.map { newLocs[it] },
          errorLoc.map { newLocs[it] },
        )
      }
  }

  val builder = XcfaBuilder(name, globalVars.toMutableSet())
  procedureBuilders.forEach { builder.addProcedure(it.copy()) }
  initProcedureBuilders.forEach { (proc, params) ->
    val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
    builder.addEntryPoint(initProc, params)
  }
  return builder.build()
}
