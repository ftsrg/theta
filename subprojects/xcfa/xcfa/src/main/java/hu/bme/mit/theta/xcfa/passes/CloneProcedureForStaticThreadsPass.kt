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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class CloneProcedureForStaticThreadsPass : ProcedurePass {

  companion object {
    private var locationCopyCounter = 0
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      var changed = false
      val updatedLabels =
        edge.getFlatLabels().map { label ->
          if (label is StartLabel) {
            val procedure = builder.parent.getProcedures().find { it.name == label.name }
              ?: return@forEach
            val fixedArgs = procedure.getParams().mapIndexed { index, param ->
              if (param.second != ParamDirection.OUT) {
                label.params[index] as? LitExpr<*>
              } else {
                null
              }
            }
            if (fixedArgs.all { it == null }) {
              return@forEach
            }

            val specializedName = "${procedure.name}__theta_specialized__" + fixedArgs.mapIndexedNotNull { index, litExpr ->
              if (litExpr != null) "arg${index}__val${litExpr}"
              else null
            }.joinToString("__")

            // Specialize procedure
            if (builder.parent.getProcedures().none { it.name == specializedName }) {
              val specializedProcedure =
                procedure.deepCopy("spec_${locationCopyCounter++}").also { it.name = specializedName }
              val init = specializedProcedure.initLoc
              val pseudoInitLoc =
                XcfaLocation("${specializedName}__init__${init.name}", metadata = init.metadata)
              init.outgoingEdges.toSet().forEach { outEdge ->
                val copiedEdge = outEdge.withSource(pseudoInitLoc)
                specializedProcedure.removeEdge(outEdge)
                specializedProcedure.addEdge(copiedEdge)
              }
              val fixArguments = fixedArgs.mapIndexedNotNull { index, arg ->
                if (arg != null) {
                  val param = specializedProcedure.getParams()[index].first
                  AssignStmtLabel(param.ref, arg, label.metadata)
                } else null
              }
              val fixLabel = SequenceLabel(fixArguments)
              specializedProcedure.addEdge(XcfaEdge(init, pseudoInitLoc, fixLabel, edge.metadata))
              builder.parent.addProcedure(specializedProcedure)
            }

            // Update start label to call specialized procedure
            changed = true
            label.copy(name = specializedName)
          } else label
        }

      if (changed) {
        val newEdge = edge.withLabel(SequenceLabel(updatedLabels))
        builder.removeEdge(edge)
        builder.addEdge(newEdge)
      }
    }
    return builder
  }
}