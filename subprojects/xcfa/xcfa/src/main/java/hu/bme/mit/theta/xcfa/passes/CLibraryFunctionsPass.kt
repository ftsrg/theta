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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms the library procedure calls with names in supportedFunctions into model elements.
 * Requires the ProcedureBuilder be `deterministic`.
 */
class CLibraryFunctionsPass(val parseContext: ParseContext) : ProcedurePass {

    private val supportedFunctions = setOf(
        "printf",
        "pthread_join",
        "pthread_create",
        "pthread_mutex_lock",
        "pthread_mutex_unlock",
        "pthread_cond_wait",
        "pthread_cond_signal",
        "pthread_mutex_init",
        "pthread_cond_init"
    )

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if (edges.size > 1 || (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        val invokeLabel = it.label.labels[0] as InvokeLabel
                        val metadata = invokeLabel.metadata
                        val labels: List<XcfaLabel> = when (invokeLabel.name) {
                            "printf" -> listOf(NopLabel)
                            "pthread_join" -> {
                                var handle = invokeLabel.params[1]
                                while (handle is Reference<*, *>) handle = handle.op
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                listOf(JoinLabel((handle as RefExpr<out Type>).decl as VarDecl<*>, metadata))
                            }

                            "pthread_create" -> {
                                var handle = invokeLabel.params[1]
                                while (handle is Reference<*, *>) handle = handle.op
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                val funcptr = invokeLabel.params[3]
                                check(funcptr is RefExpr && (funcptr as RefExpr<out Type>).decl is VarDecl)

                                val param = invokeLabel.params[4]

                                listOf(StartLabel((funcptr as RefExpr<out Type>).decl.name,
                                    listOf(Int(0), param), // int(0) to solve StartLabel not handling return params
                                    (handle as RefExpr<out Type>).decl as VarDecl<*>, metadata))
                            }

                            "pthread_mutex_lock" -> {
                                var handle = invokeLabel.params[1]
                                while (handle is Reference<*, *>) handle = handle.op
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                listOf(FenceLabel(setOf("mutex_lock(${handle.decl.name})"), metadata))
                            }

                            "pthread_mutex_unlock" -> {
                                var handle = invokeLabel.params[1]
                                while (handle is Reference<*, *>) handle = handle.op
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                listOf(FenceLabel(setOf("mutex_unlock(${handle.decl.name})"), metadata))
                            }

                            "pthread_cond_wait" -> {
                                var cond = invokeLabel.params[1]
                                while (cond is Reference<*, *>) cond = cond.op
                                var handle = invokeLabel.params[2]
                                while (handle is Reference<*, *>) handle = handle.op
                                check(cond is RefExpr && (cond as RefExpr<out Type>).decl is VarDecl)
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                listOf(
                                    FenceLabel(setOf("start_cond_wait(${cond.decl.name},${handle.decl.name})"),
                                        metadata),
                                    FenceLabel(setOf("cond_wait(${cond.decl.name},${handle.decl.name})"), metadata)
                                )
                            }

                            "pthread_cond_signal" -> {
                                var cond = invokeLabel.params[1]
                                while (cond is Reference<*, *>) cond = cond.op
                                check(cond is RefExpr && (cond as RefExpr<out Type>).decl is VarDecl)

                                listOf(FenceLabel(setOf("cond_signal(${cond.decl.name})"), metadata))
                            }

                            "pthread_mutex_init", "pthread_cond_init" -> listOf(NopLabel)

                            else -> error("Unsupported library function ${invokeLabel.name}")
                        }
                        edge.withLabel(SequenceLabel(labels)).splitIf { label ->
                            label is FenceLabel && label.labels.any { l -> l.startsWith("start_cond_wait") }
                        }.forEach(builder::addEdge)
                    } else {
                        builder.addEdge(edge.withLabel(SequenceLabel(it.label.labels)))
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