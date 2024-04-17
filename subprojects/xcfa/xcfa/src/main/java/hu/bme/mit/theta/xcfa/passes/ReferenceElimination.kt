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
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.getReferences
import hu.bme.mit.theta.xcfa.model.*

/**
 * Removes all references in favor of creating arrays instead.
 */

class ReferenceElimination(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])

        val referredVars = builder.getEdges()
            .flatMap { it.label.getFlatLabels().flatMap { getReferences(it) } }
            .map { (it.expr as RefExpr<*>).decl as VarDecl<*> }
            .associateWith {
                val ptrType = CPointer(null, CComplexType.getType(it.ref, parseContext), parseContext)
                val varDecl = Var(it.name + "*", ptrType.smtType)
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

        return builder
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

                is StmtLabel -> StmtLabel(stmt.changeReferredVars(varLut, parseContext), metadata = metadata,
                    choiceType = this.choiceType)

                else -> this
            }
        else this

    @JvmOverloads
    fun Stmt.changeReferredVars(varLut: Map<out Decl<*>, VarDecl<*>>, parseContext: ParseContext? = null): Stmt {
        val stmt = when (this) {
            is AssignStmt<*> -> if(this.varDecl in varLut.keys) {
                val newVar = varLut[this.varDecl]!!
                AssignStmt.of(cast(newVar, newVar.type), cast(ArrayWriteExpr.of(newVar.ref as Expr<ArrayType<Type, Type>>, CComplexType.getSignedInt(parseContext).nullValue as Expr<Type>, this.expr.changeReferredVars(varLut, parseContext) as Expr<Type>), newVar.type))
            } else {
                AssignStmt.of(cast(this.varDecl, this.varDecl.type), cast(this.expr.changeReferredVars(varLut, parseContext), this.varDecl.type))
            }

            is AssumeStmt -> AssumeStmt.of(cond.changeReferredVars(varLut, parseContext))
            is SequenceStmt -> SequenceStmt.of(stmts.map { it.changeReferredVars(varLut, parseContext) })
            is SkipStmt -> this
            else -> TODO("Not yet implemented")
        }
        val metadataValue = parseContext?.getMetadata()?.getMetadataValue(this, "sourceStatement")
        if (metadataValue?.isPresent == true)
            parseContext.getMetadata().create(stmt, "sourceStatement", metadataValue.get())
        return stmt
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
        varLut[this]?.let { ArrayReadExpr.of(it.ref as Expr<ArrayType<Type, T>>, CComplexType.getSignedInt(parseContext).nullValue as Expr<Type>) as Expr<T> } ?: this.ref

}