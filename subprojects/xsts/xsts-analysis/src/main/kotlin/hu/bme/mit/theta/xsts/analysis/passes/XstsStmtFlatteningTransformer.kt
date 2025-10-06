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
package hu.bme.mit.theta.xsts.analysis.passes

import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xsts.XSTS

object XstsStmtFlatteningTransformer {

    fun transform(xsts: XSTS, depth: Int): XSTS {

        /*

        Flattens the statements up to a given depth.

        */

        if (depth == 0) return xsts

        val envFlattened = flattenStmts(xsts.env, depth)
        val tranFlattened = flattenStmts(xsts.tran, depth)

        return XSTS(
            xsts.stateVars,
            xsts.localVars,
            xsts.ctrlVars,
            xsts.init,
            NonDetStmt.of(tranFlattened.toList()),
            NonDetStmt.of(envFlattened.toList()),
            xsts.initFormula,
            xsts.prop,
        )
    }

    private fun cartesianProduct(vararg sets: Set<*>): Set<kotlin.collections.List<*>> =
        sets
            .fold(listOf(listOf<Any?>())) { acc, set ->
                acc.flatMap { list -> set.map { element -> list + element } }
            }
            .toSet()

    private fun flattenStmts(stmt: Stmt, maxDepth: Int = -1, currentDepth: Int = 0): Set<Stmt> {
        if (maxDepth != -1 && currentDepth > maxDepth) {
            return setOf(stmt)
        }
        return when (stmt) {
            is NonDetStmt -> {
                stmt.stmts.flatMap { flattenStmts(it, maxDepth, if (stmt.stmts.size > 1) currentDepth + 1 else currentDepth) }.toSet()
            }

            is SequenceStmt -> {
                cartesianProduct(
                    *(stmt.stmts.map { flattenStmts(it, maxDepth, if (stmt.stmts.size > 1) currentDepth + 1 else currentDepth) }
                        .toTypedArray())
                )
                    .map { SequenceStmt.of(it as kotlin.collections.List<Stmt>) }
                    .toSet()
            }

            is IfStmt -> {
                flattenStmts(stmt.then, maxDepth, currentDepth + 1) + flattenStmts(stmt.elze, maxDepth, currentDepth + 1)
            }

            else -> {
                setOf(stmt)
            }
        }
    }

    fun XSTS.events(): List<Event<VarDecl<*>>> {

        val flattened = flattenStmts(SequenceStmt.of(listOf(env, tran)), 5)
        return flattened.map {
            object : Event<VarDecl<*>> {
                override fun getAffectedVars(): List<VarDecl<*>> =
                    StmtUtils.getWrittenVars(it).toList()
            }
        }.toList()

    }
}
