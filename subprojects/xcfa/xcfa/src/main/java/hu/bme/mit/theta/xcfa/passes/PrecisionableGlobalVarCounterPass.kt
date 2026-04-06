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

import hu.bme.mit.theta.analysis.algorithm.PorLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.*

class PrecisionableGlobalVarCounterPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (PorLogger.precisionableGlobalVarCount == null) {
      val xcfa = builder.parent
      val globalVars = xcfa.getVars().map { it.wrappedVar }
      val usedGlobalVars = mutableSetOf<VarDecl<*>>()
      xcfa.getProcedures().forEach { proc ->
        proc.getEdges().forEach { edge ->
          usedGlobalVars.addAll(edge.label.precisionableVars().filter { it in globalVars })
        }
      }
      PorLogger.precisionableGlobalVarCount = usedGlobalVars.size
    }
    return builder
  }

  private fun XcfaLabel.precisionableVars(): Collection<VarDecl<*>> =
    when (this) {
      is StmtLabel -> StmtUtils.getVars(stmt)
      is NondetLabel -> labels.flatMap { it.precisionableVars() }
      is SequenceLabel -> labels.flatMap { it.precisionableVars() }
      is InvokeLabel -> params.flatMap { ExprUtils.getVars(it) }
      is JoinLabel -> setOf()
      is StartLabel -> params.flatMap { ExprUtils.getVars(it) }.toSet()
      is FenceLabel ->
        when (this) {
          is AtomicFenceLabel -> setOf()
          is MutexTryLockLabel -> setOf(successVar)
          else -> setOf()
        }
      else -> emptySet()
    }
}
