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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Neq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms calls to `assert(cond)` into two edges: one to the error location guarded by
 * `assume(!cond)` (the failing branch), and one continuing to the original target guarded by
 * `assume(cond)` (the passing branch). Requires the ProcedureBuilder be `deterministic`.
 */
class AssertionToErrorLocationPass(private val property: XcfaProperty) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (property.inputProperty != ErrorDetection.NO_ASSERTION_VIOLATION) return builder
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          val label = (it.label as SequenceLabel).labels[0]
          if (predicate(label)) {
            val assertLabel = label as InvokeLabel
            // params convention: c2xcfa puts the return-value slot first, then arguments.
            // For assert(cond), the condition is always the last param.
            val cond = getCondition(assertLabel.params.last())

            if (builder.errorLoc.isEmpty) builder.createErrorLoc()

            builder.addEdge(
              XcfaEdge(
                it.source,
                builder.errorLoc.get(),
                SequenceLabel(
                  listOf(StmtLabel(Stmts.Assume(Not(cond)), metadata = label.metadata)),
                  metadata = label.metadata,
                ),
                metadata = label.metadata,
              )
            )

            builder.addEdge(
              XcfaEdge(
                it.source,
                it.target,
                SequenceLabel(
                  listOf(StmtLabel(Stmts.Assume(cond), metadata = label.metadata)),
                  metadata = label.metadata,
                ),
                metadata = label.metadata,
              )
            )
          } else {
            builder.addEdge(it)
          }
        }
      }
    }
    return builder
  }

  private fun predicate(it: XcfaLabel): Boolean = it is InvokeLabel && it.name == "assert"

  @Suppress("UNCHECKED_CAST")
  private fun getCondition(param: Expr<*>): Expr<BoolType> =
    when {
      param.type is BoolType -> param as Expr<BoolType>
      param.type is IntType -> Neq(param as Expr<IntType>, Int(0))
      else ->
        throw IllegalArgumentException(
          "Unsupported assert condition type: ${param.type}. Expected Bool or Int."
        )
    }
}
