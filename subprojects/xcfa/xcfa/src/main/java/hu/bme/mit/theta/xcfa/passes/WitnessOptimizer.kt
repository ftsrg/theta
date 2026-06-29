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

import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intersect
import hu.bme.mit.theta.xcfa.utils.simplify

class WitnessOptimizer(private val params: List<Expr<*>>, private val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val initialValuation = MutableValuation()
    builder.getParams().forEachIndexed { index, param ->
      if (param.second == ParamDirection.IN && index < params.size && params[index] is LitExpr<*>) {
        initialValuation.put(param.first, params[index] as LitExpr<*>)
      }
    }

    val waitlist = mutableMapOf(builder.initLoc to mutableListOf(initialValuation))
    while (waitlist.isNotEmpty()) {
      val (loc, valuations) = waitlist.firstNotNullOf { (loc, valuations) ->
        if (valuations.size >= loc.incomingEdges.size) loc to valuations else null
      }
      waitlist.remove(loc)
      val mergedValuation = MutableValuation.copyOf(valuations.reduce(::intersect))

      loc.outgoingEdges.toList().forEach { edge ->
        val oldLabels = edge.getFlatLabels()
        val newLabels = oldLabels.flatMap {
          val simplified = it.simplify(mergedValuation, parseContext)
          simplifySegmentCounterAssignment(simplified)
            ?: simplifyStartLabelLogicalThread(simplified)
            ?: listOf(simplified)
        }.filter {
          if (it is StmtLabel) {
            val stmt = it.stmt
            if (stmt is AssignStmt<*> && stmt.varDecl.name == SEGMENT_COUNTER) {
              val expr = stmt.expr
              if (expr is RefExpr<*> && expr.decl.name == SEGMENT_COUNTER) {
                return@filter false
              }
            }
          }
          true
        }
        builder.parent.getVars().forEach { mergedValuation.remove(it.wrappedVar) }

        if (newLabels != oldLabels) {
          builder.removeEdge(edge)
          builder.addEdge(edge.withLabel(SequenceLabel(newLabels)))
        }
        waitlist.getOrPut(edge.target) { mutableListOf() }.add(mergedValuation)
      }
    }

    return builder
  }

  private fun simplifySegmentCounterAssignment(label: XcfaLabel): List<XcfaLabel>? {
    if (label is StmtLabel) {
      val stmt = label.stmt
      if (stmt is AssignStmt<*>) {
        if (stmt.varDecl.name == SEGMENT_COUNTER) {
          val expr = stmt.expr
          if (expr is IteExpr<*>) {
            val cond = expr.cond
            val then = expr.then
            if (cond is EqExpr<*> && then is LitExpr<*>) {
              return listOf(StmtLabel(AssumeStmt.of(cond)), AssignStmtLabel(stmt.varDecl, then, label.metadata))
            }
          }
        }
      }
    }
    return null
  }

  private fun simplifyStartLabelLogicalThread(label: XcfaLabel): List<XcfaLabel>? {
    if (label !is StartLabel) return null
    var assumption: AssumeStmt? = null
    val newParams = label.params.map {
      if (it is IteExpr) {
        val cond = it.cond
        val then = it.then
        if (cond is EqExpr<*> && then is LitExpr<*>) {
          val left = cond.leftOp
          if (left is RefExpr<*> && left.decl.name == SEGMENT_COUNTER) {
            assumption = AssumeStmt.of(cond)
            return@map then
          }
        }
      }
      it
    }
    if (assumption == null) return null
    return listOf(StmtLabel(assumption), label.copy(params = newParams))
  }
}