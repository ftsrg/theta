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

import hu.bme.mit.theta.core.clock.constr.ClockConstrs
import hu.bme.mit.theta.core.clock.op.ClockOps
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.ExprUtils.simplify
import hu.bme.mit.theta.xcfa.model.ClockDelayLabel
import hu.bme.mit.theta.xcfa.model.ClockOpLabel
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

class ClockLabelPass() : ProcedurePass {

    private val supportedFunctions =
        setOf(
            "theta_clock_reset",
            "theta_clock_assume",
            "theta_clock_delay",
            "theta_elapsed_time",
        )

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if (edges.size > 1 ||
                    (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        val invokeLabel = it.label.labels[0] as InvokeLabel
                        val metadata = invokeLabel.metadata
                        val labels: List<XcfaLabel> = when (invokeLabel.name) {
                            "theta_clock_reset" -> {
                                val clockRef = invokeLabel.params[1]
                                check(clockRef is RefExpr && clockRef.type is RatType)
                                val clockVar = clockRef.decl as VarDecl<RatType>

                                val value = invokeLabel.params[2]
                                check(value.type is IntType)
                                val intValue = (simplify(value) as IntLitExpr).value.intValueExact()

                                listOf(ClockOpLabel(ClockOps.Reset(clockVar, intValue), metadata))
                            }

                            "theta_clock_assume" -> {
                                val expr = invokeLabel.params[1]
                                val clockExpr = if (expr is IteExpr) {
                                    check(expr.then.equals(IntExprs.Int(1)) && expr.`else`.equals(IntExprs.Int(0)))
                                    expr.cond
                                } else {
                                    expr
                                }
                                check(clockExpr.type is BoolType && clockExpr.ops.all { it.type is RatType })
                                val clockConstr = ClockConstrs.fromExpr(clockExpr as Expr<BoolType>)

                                listOf(ClockOpLabel(ClockOps.Guard(clockConstr), metadata))
                            }

                            "theta_clock_delay" -> {
                                listOf(ClockDelayLabel(metadata))
                            }

                            "theta_elapsed_time" -> {
                                val clockRef = invokeLabel.params[1]
                                check(clockRef is RefExpr && clockRef.type is RatType)
                                val threadClock = clockRef.decl as VarDecl<RatType>
                                check(threadClock.name == "thread_clock")

                                val minTimeExpr = invokeLabel.params[2]
                                val maxTimeExpr = invokeLabel.params[3]
                                check(minTimeExpr.type is IntType && maxTimeExpr.type is IntType)
                                val minTime = (simplify(minTimeExpr) as IntLitExpr).value.intValueExact()
                                val maxTime = (simplify(maxTimeExpr) as IntLitExpr).value.intValueExact()

                                listOf(
                                    ClockOpLabel(ClockOps.Guard(ClockConstrs.Geq(threadClock, minTime)), metadata),
                                    ClockOpLabel(ClockOps.Guard(ClockConstrs.Leq(threadClock, maxTime)), metadata),
                                    ClockOpLabel(ClockOps.Reset(threadClock, 0), metadata),
                                )
                            }

                            else -> error("Unsupported clock function ${invokeLabel.name}")
                        }
                        builder.addEdge(XcfaEdge(it.source, it.target, SequenceLabel(labels), metadata))
                    } else {
                        builder.addEdge(it.withLabel(SequenceLabel(it.label.labels)))
                    }
                }
            }
        }
        return builder
    }

    private fun predicate(it: XcfaLabel): Boolean {
        return it is InvokeLabel && it.name in supportedFunctions
    }
}
