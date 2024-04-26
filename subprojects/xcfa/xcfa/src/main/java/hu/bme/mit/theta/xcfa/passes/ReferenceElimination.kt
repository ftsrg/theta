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

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.references

/**
 * Removes all references in favor of creating arrays instead.
 */

class ReferenceElimination(val parseContext: ParseContext) : ProcedurePass {

    private var cnt = 2 // counts upwards, uses 3k+2
        get() = field.also { field += 2 }

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        val referredVars = builder.getEdges()
            .flatMap { it.label.getFlatLabels().flatMap { it.references } }
            .map { (it.expr as RefExpr<*>).decl as VarDecl<*> }
            .associateWith {
                val ptrType = CPointer(null, CComplexType.getType(it.ref, parseContext), parseContext)
                val varDecl = Var(it.name + "*", ptrType.smtType)
                builder.addVar(varDecl)
                parseContext.metadata.create(varDecl.ref, "cType", ptrType)
                varDecl
            }
        
        if (referredVars.isEmpty()) {
            return builder
        }

        val edges = LinkedHashSet(builder.getEdges())
        for (edge in edges) {
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.changeReferredVars(referredVars, parseContext)))
        }

        return DeterministicPass().run(NormalizePass().run(builder))
    }

    @JvmOverloads
    fun XcfaLabel.changeReferredVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): XcfaLabel =
        if (varLut.isNotEmpty())
            when (this) {
                is InvokeLabel -> InvokeLabel(name, params.map { it.changeReferredVars(varLut, parseContext) },
                    metadata = metadata)

                is NondetLabel -> NondetLabel(labels.map { it.changeReferredVars(varLut, parseContext) }.toSet(),
                    metadata = metadata)

                is SequenceLabel -> SequenceLabel(labels.map { it.changeReferredVars(varLut, parseContext) },
                    metadata = metadata)

                is StartLabel -> StartLabel(name, params.map { it.changeReferredVars(varLut, parseContext) },
                    pidVar, metadata = metadata)

                is StmtLabel -> SequenceLabel(stmt.changeReferredVars(varLut, parseContext).map {
                    StmtLabel(it, metadata = metadata,
                        choiceType = this.choiceType)
                }).let { if (it.labels.size == 1) it.labels[0] else it }

                else -> this
            }
        else this

    @JvmOverloads
    fun Stmt.changeReferredVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): List<Stmt> {
        val stmts = when (this) {
            is AssignStmt<*> -> if(this.varDecl in varLut.keys) {
                val newVar = varLut[this.varDecl]!!
                listOf(
                    AssignStmt.of(cast(newVar, newVar.type),
                        cast(CComplexType.getType(newVar.ref, parseContext).getValue("$cnt"),
                            newVar.type)),
                    MemoryAssignStmt.create(
                        Dereference(
                            cast(newVar.ref, newVar.type),
                            cast(CComplexType.getSignedInt(parseContext).nullValue, newVar.type),
                            CPointer(null, CComplexType.getType(expr, parseContext), parseContext).smtType),
                        this.expr.changeReferredVars(varLut, parseContext)))
            } else {
                listOf(AssignStmt.of(cast(this.varDecl, this.varDecl.type),
                    cast(this.expr.changeReferredVars(varLut, parseContext), this.varDecl.type)))
            }

            is MemoryAssignStmt<*, *> -> listOf(
                MemoryAssignStmt.create(deref.changeReferredVars(varLut, parseContext) as Dereference<*, *>,
                    expr.changeReferredVars(varLut, parseContext)))

            is AssumeStmt -> listOf(AssumeStmt.of(cond.changeReferredVars(varLut, parseContext)))
            is SequenceStmt -> listOf(
                SequenceStmt.of(this.stmts.flatMap { it.changeReferredVars(varLut, parseContext) }))

            is SkipStmt -> listOf(this)
            else -> TODO("Not yet implemented ($this)")
        }
        val metadataValue = parseContext?.metadata?.getMetadataValue(this, "sourceStatement")
        if (metadataValue?.isPresent == true) {
            for (stmt in stmts) {
                parseContext.metadata.create(stmt, "sourceStatement", metadataValue.get())
            }
        }
        return stmts
    }

    @JvmOverloads
    fun <T : Type> Expr<T>.changeReferredVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): Expr<T> =
        if (this is RefExpr<T>) {
            (decl as Decl<T>).changeReferredVars(varLut)
        }
        else if (this is Reference<*, *> && this.expr is RefExpr<*> && (this.expr as RefExpr<*>).decl in varLut.keys) {
            varLut[(this.expr as RefExpr<*>).decl]?.ref as Expr<T>
        }
        else {
            val ret = this.withOps(this.ops.map { it.changeReferredVars(varLut, parseContext) })
            if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
                parseContext.metadata?.create(ret, "cType", CComplexType.getType(this, parseContext))
            }
            ret
        }

    fun <T : Type> Decl<T>.changeReferredVars(varLut: Map<out Decl<*>, VarDecl<*>>): Expr<T> =
        varLut[this]?.let { Dereference(cast(it.ref, it.type), cast(CComplexType.getSignedInt(parseContext).nullValue, this.ref.type), it.type) as Expr<T> } ?: this.ref

}