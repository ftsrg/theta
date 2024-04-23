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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.dereferences
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger

/**
 * Transforms derefs into variables if possible (in the entire XCFA, no derefs remain non-literal)
 * Requires the ProcedureBuilder be `deterministic`.
 */
class LiteralDerefPass(val parseContext: ParseContext) : ProcedurePass {

    private var cnt = 0
        get() = field++

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        val localDerefs = builder.getEdges().flatMap { it.getFlatLabels().flatMap { it.dereferences } }
            .filter { it.array is LitExpr<*> && it.offset is LitExpr }

        if (localDerefs.isNotEmpty()) {
            val varValLut = builder.parent.heapMap.ifEmpty {
                val derefs = builder.parent.getProcedures()
                    .flatMap { it.getEdges().flatMap { it.getFlatLabels().flatMap { it.dereferences } } }
                    .filter { it.array is LitExpr<*> && it.offset is LitExpr }
                val derefValLut = derefs.associateWith { it.triple }

                val ret = derefValLut.values.associateWith { Var("__heap__$cnt", it.third) }
                builder.parent.heapMap.putAll(ret)
                ret
            }
            val derefVarLut = localDerefs.associateWith {deref -> varValLut[Triple(toValue(deref.array as LitExpr<*>).toInt(), toValue(deref.offset as LitExpr<*>).toInt(),
                deref.type)]!! }

            val edges = builder.getEdges().filter { it.label.dereferences.isNotEmpty() }.toSet()
            for (edge in edges) {
                builder.removeEdge(edge)
                builder.addEdge(edge.withLabel(edge.label.replaceDeref(derefVarLut)))
            }

            return DeterministicPass().run(NormalizePass().run(builder))
        }

        return builder
    }

    private val toValue: (LitExpr<*>) -> BigInteger = {
        if (it is IntLitExpr) it.value else BvUtils.neutralBvLitExprToBigInteger(it as BvLitExpr)
    }

    private val Dereference<*, *>.triple: Triple<Int, Int, Type>
        get() = Triple(toValue(array as LitExpr<*>).toInt(), toValue(offset as LitExpr<*>).toInt(), type)

    private fun Dereference<*, *>.assumption(dereference: Dereference<*, *>) =
        AssumeStmt.of(And(Eq(dereference.array, array), Eq(dereference.offset, offset)))


    private fun MemoryAssignStmt<*, *>.assignment(lut: Map<Dereference<*, *>, VarDecl<*>>) =
        AssignStmt.of(cast(lut[deref]!!, deref.type), cast(expr.replaceDeref(lut), deref.type))


    private fun XcfaLabel.replaceDeref(lut: Map<Dereference<*, *>, VarDecl<*>>): XcfaLabel =
        when(this) {
            is InvokeLabel -> InvokeLabel(this.name, this.params.map{it.replaceDeref(lut)}, metadata, tempLookup)
            is NondetLabel -> NondetLabel(labels.map { it.replaceDeref(lut) }.toSet(), metadata)
            is SequenceLabel -> SequenceLabel(labels.map { it.replaceDeref(lut) }, metadata)
            is StartLabel -> StartLabel(name, params.map { it.replaceDeref(lut) }, pidVar, metadata, tempLookup)
            is StmtLabel -> stmt.replaceDeref(lut).let {
                if (it.size == 1)
                    StmtLabel(it[0], choiceType, metadata)
                else
                    NondetLabel(it.map {
                        it as SequenceStmt
                        SequenceLabel(it.stmts.map { StmtLabel(it, choiceType, metadata) }, metadata)
                    }.toSet())
            }
            else -> error("Not implemented for ${this.javaClass.simpleName}")
        }

    private fun Stmt.replaceDeref(lut: Map<Dereference<*, *>, VarDecl<*>>): List<Stmt> =
        when(this) {
            is MemoryAssignStmt<*, *> -> if(this.deref in lut)
                listOf(this.assignment(lut))
            else {
                lut.map { SequenceStmt.of(listOf(it.key.assumption(deref), this.assignment(lut))) } + SequenceStmt.of(
                    listOf(AssumeStmt.of(Not(Or(lut.map { it.key.assumption(deref).cond }))), this))
            }
            is AssignStmt<*> -> listOf(AssignStmt.of(cast(varDecl, varDecl.type), cast(expr.replaceDeref(lut), varDecl.type)))
            is AssumeStmt -> listOf(AssumeStmt.of(cond.replaceDeref(lut) as Expr<BoolType>))
            else -> listOf(this)
        }

    // TODO: this should also be aware of non-literal dereferences
    private fun Expr<*>.replaceDeref(lut: Map<Dereference<*, *>, VarDecl<*>>): Expr<*> =
        if(this in lut) {
            lut[this]!!.ref
        } else {
            withOps(ops.map { it.replaceDeref(lut) })
        }
}