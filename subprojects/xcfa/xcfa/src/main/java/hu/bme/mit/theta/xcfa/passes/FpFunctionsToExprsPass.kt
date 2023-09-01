/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import com.google.common.base.Preconditions
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.fptype.*
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.BiFunction

//TODO: type-right conversions (because sqrt and sqrtf might have different domains)
class FpFunctionsToExprsPass(val parseContext: ParseContext) : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val newStmts: MutableList<XcfaLabel> = ArrayList()
            var found = false
            for (stmt in (edge.label as SequenceLabel).labels) {
                if (stmt is InvokeLabel) {
                    if (handlers.containsKey(stmt.name)) {
                        newStmts.add(checkNotNull(handlers[stmt.name]).apply(builder, stmt))
                        found = true
                    }
                } else newStmts.add(stmt)
            }
            if (found) {
                builder.removeEdge(edge)
                builder.addEdge(XcfaEdge(edge.source, edge.target, SequenceLabel(newStmts)))
            }
        }
        return builder
    }

    private val handlers: MutableMap<String, BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>> = LinkedHashMap()
    private fun addHandler(names: Array<String>,
        handler: BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>) {
        for (name in names) {
            handlers[name] = handler
        }
    }

    init {
        addHandler(arrayOf("fabs", "fabsf",
            "fabsl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFabs(builder, callStmt)
        }
        addHandler(arrayOf("floor", "floorf",
            "floorl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFloor(builder, callStmt)
        }
        addHandler(arrayOf("fmax", "fmaxf",
            "fmaxl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFmax(builder, callStmt)
        }
        addHandler(arrayOf("fmin", "fminf",
            "fminl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFmin(builder, callStmt)
        }
        addHandler(arrayOf("fmod", "fmodf",
            "fmodl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFmod(builder, callStmt)
        }
        addHandler(arrayOf("sqrt", "sqrtf",
            "sqrtl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleSqrt(builder, callStmt)
        }
        addHandler(arrayOf("round", "roundf",
            "roundl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleRound(builder, callStmt)
        }
        addHandler(arrayOf("isnan")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleIsnan(builder, callStmt)
        }
        addHandler(arrayOf("trunc")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleTrunc(builder, callStmt)
        }
        addHandler(arrayOf("ceil")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleCeil(builder, callStmt)
        }
        addHandler(arrayOf(
            "isnormal")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleIsnormal(builder, callStmt)
        }
        addHandler(arrayOf("isinf", "__isinf", "__isinff",
            "__isinfl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleIsinf(builder, callStmt)
        }
        addHandler(arrayOf(
            "isfinite")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleIsfinite(builder, callStmt)
        }
        addHandler(arrayOf("__fpclassify", "__fpclassifyf",
            "__fpclassifyl")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
            handleFpclassify(builder, callStmt)
        }
    }

    private fun handleTrunc(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpRoundToIntegralExpr.of(FpRoundingMode.RTZ, callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleCeil(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpRoundToIntegralExpr.of(FpRoundingMode.RTP, callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleIsinf(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val type = CSignedInt(null, parseContext)
        val assign: AssignStmt<*> = Stmts.Assign(
            TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
            TypeUtils.cast(AbstractExprs.Ite<Type>(
                FpIsInfiniteExpr.of(callStmt.params[1] as Expr<FpType?>), type.unitValue, type.nullValue),
                type.smtType))
        parseContext.metadata.create(assign.expr, "cType", type)
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleIsfinite(builder: XcfaProcedureBuilder,
        callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val type = CSignedInt(null, parseContext)
        val assign: AssignStmt<*> = Stmts.Assign(
            TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
            TypeUtils.cast(AbstractExprs.Ite<Type>(
                FpIsInfiniteExpr.of(callStmt.params[1] as Expr<FpType?>), type.nullValue, type.unitValue),
                type.smtType))
        parseContext.metadata.create(assign.expr, "cType", type)
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleIsnormal(builder: XcfaProcedureBuilder,
        callStmt: InvokeLabel): XcfaLabel {
        throw UnsupportedOperationException()
    }

    private fun handleFpclassify(builder: XcfaProcedureBuilder,
        callStmt: InvokeLabel): XcfaLabel {
        throw UnsupportedOperationException()
    }

    private fun handleIsnan(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            val type = CComplexType.getType(expr, parseContext)
            val assign: AssignStmt<*> = Stmts.Assign(
                TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
                TypeUtils.cast(
                    AbstractExprs.Ite<Type>(FpIsNanExpr.of(callStmt.params[1] as Expr<FpType?>),
                        type.unitValue, type.nullValue), type.smtType))
            parseContext.getMetadata().create(assign.expr, "cType", type)
            return StmtLabel(assign, metadata = callStmt.metadata)
        } else {
            throw UnsupportedOperationException("Not yet supported without cType")
        }
    }

    private fun handleRound(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpRoundToIntegralExpr.of(FpRoundingMode.RNA, callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleSqrt(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpSqrtExpr.of(FpRoundingMode.RNE, callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleFmod(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        throw UnsupportedOperationException("Fmod not yet supported!")
    }

    private fun handleFmin(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 3,
            "Function is presumed to be binary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpMinExpr.of(callStmt.params[1] as Expr<FpType?>,
                callStmt.params[2] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleFmax(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 3,
            "Function is presumed to be binary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpMaxExpr.of(callStmt.params[1] as Expr<FpType?>,
                callStmt.params[2] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleFloor(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpRoundToIntegralExpr.of(FpRoundingMode.RTN, callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }

    private fun handleFabs(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
        Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
        val expr = callStmt.params[0]
        Preconditions.checkState(expr is RefExpr<*>)
        val assign = Stmts.Assign((expr as RefExpr<*>).decl as VarDecl<FpType>,
            FpAbsExpr.of(callStmt.params[1] as Expr<FpType?>))
        if (parseContext.getMetadata().getMetadataValue(expr, "cType").isPresent) {
            parseContext.getMetadata().create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
        }
        return StmtLabel(assign, metadata = callStmt.metadata)
    }
}