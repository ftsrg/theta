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

package hu.bme.mit.theta.frontend.dve.grammar

import hu.bme.mit.theta.dve.frontend.dsl.gen.dveBaseVisitor
import hu.bme.mit.theta.dve.frontend.dsl.gen.dveParser
import hu.bme.mit.theta.frontend.dve.model.*

/**
 * Builds a [DveModel] from an ANTLR parse tree.
 *
 * Qualified identifiers of the form `ProcessName.identifier` are syntactically
 * ambiguous: `identifier` may be either a variable name or a state name in that
 * process. Resolution is done in a two-phase approach:
 *  1. Pre-scan: collect every process name → set of state names before visiting.
 *  2. Main visit: resolve every [dveParser.QualifiedRefContext] and
 *     [dveParser.QualifiedArrayRefContext] using the collected state sets.
 *
 * Private helpers are prefixed with `build` rather than `visit` to avoid
 * shadowing the ANTLR-generated visitor methods in [dveBaseVisitor].
 */
class DveModelVisitor : dveBaseVisitor<Any>() {

    /** Map from process name to its declared state names, populated during pre-scan. */
    private val processStates = mutableMapOf<String, Set<String>>()

    // -------------------------------------------------------------------------
    // Top-level
    // -------------------------------------------------------------------------

    override fun visitModel(ctx: dveParser.ModelContext): DveModel {
        // Phase 1: collect state names for all processes
        ctx.processDecl().forEach { proc ->
            val name = proc.ID().text
            val states = proc.processBody().stateDecl().idList().ID().map { it.text }.toSet()
            processStates[name] = states
        }

        val globalVars = mutableListOf<DveVarOrArrayDecl>()
        val channels = mutableListOf<DveChannelDecl>()

        for (decl in ctx.topDecl()) {
            when {
                decl.varDecl() != null -> globalVars += buildScalarDecl(decl.varDecl())
                decl.arrayDecl() != null -> globalVars += buildArrayDecl(decl.arrayDecl())
                decl.channelDecl() != null -> channels += buildChannelDecl(decl.channelDecl())
            }
        }

        val processes = ctx.processDecl().map { buildProcess(it) }
        val system = buildSystemDecl(ctx.systemDecl())

        return DveModel(
            globalVariables = globalVars,
            channels = channels,
            processes = processes,
            system = system,
        )
    }

    // -------------------------------------------------------------------------
    // Variable and array declarations
    // -------------------------------------------------------------------------

    private fun buildScalarDecl(ctx: dveParser.VarDeclContext): DveVarOrArrayDecl.Scalar =
        DveVarOrArrayDecl.Scalar(
            DveVariableDecl(
                name = ctx.ID().text,
                type = buildVarType(ctx.varType()),
                initialValue = ctx.expr()?.let { buildExpr(it) },
            )
        )

    private fun buildArrayDecl(ctx: dveParser.ArrayDeclContext): DveVarOrArrayDecl.Array =
        DveVarOrArrayDecl.Array(
            DveArrayDecl(
                name = ctx.ID().text,
                type = buildVarType(ctx.varType()),
                size = ctx.INT_LITERAL().text.toInt(),
                initialValues = ctx.exprList()?.expr()?.map { buildExpr(it) },
            )
        )

    private fun buildVarType(ctx: dveParser.VarTypeContext): DveVariableType =
        if (ctx.BYTE() != null) DveVariableType.BYTE else DveVariableType.INT

    // -------------------------------------------------------------------------
    // Channel declarations
    // -------------------------------------------------------------------------

    private fun buildChannelDecl(ctx: dveParser.ChannelDeclContext): DveChannelDecl =
        when (ctx) {
            is dveParser.SyncNoDataChannelContext ->
                DveChannelDecl(
                    name = ctx.ID().text,
                    typedFields = emptyList(),
                    bufferSize = ctx.INT_LITERAL().text.toInt(),
                )
            is dveParser.TypedChannelContext ->
                DveChannelDecl(
                    name = ctx.ID().text,
                    typedFields = ctx.varTypeList().varType().map { buildVarType(it) },
                    bufferSize = ctx.INT_LITERAL().text.toInt(),
                )
            else -> error("Unknown channel decl: $ctx")
        }

    // -------------------------------------------------------------------------
    // Process declarations
    // -------------------------------------------------------------------------

    private fun buildProcess(ctx: dveParser.ProcessDeclContext): DveProcess {
        val name = ctx.ID().text
        val body = ctx.processBody()

        val localVars = buildList {
            body.localDecl().forEach { ld ->
                when {
                    ld.varDecl() != null -> add(buildScalarDecl(ld.varDecl()))
                    ld.arrayDecl() != null -> add(buildArrayDecl(ld.arrayDecl()))
                }
            }
        }

        val states = body.stateDecl().idList().ID().map { it.text }
        val initialState = body.initDecl().ID().text
        val acceptingStates = body.acceptDecl().flatMap { it.idList().ID().map { id -> id.text } }
        val committedStates = body.commitDecl().flatMap { it.idList().ID().map { id -> id.text } }
        val assertions = body.assertDecl()?.assertItem()?.map { buildAssertion(it) } ?: emptyList()
        val transitions = body.transPart()?.transition()?.map { buildTransition(it) } ?: emptyList()

        return DveProcess(
            name = name,
            variables = localVars,
            states = states,
            initialState = initialState,
            acceptingStates = acceptingStates,
            committedStates = committedStates,
            assertions = assertions,
            transitions = transitions,
        )
    }

    private fun buildAssertion(ctx: dveParser.AssertItemContext): DveAssertion =
        DveAssertion(stateName = ctx.ID().text, expression = buildExpr(ctx.expr()))

    // -------------------------------------------------------------------------
    // Transitions
    // -------------------------------------------------------------------------

    private fun buildTransition(ctx: dveParser.TransitionContext): DveTransition {
        var guard: DveExpression? = null
        var sync: DveSyncAction? = null
        val effects = mutableListOf<DveAssignment>()

        for (clause in ctx.transClause()) {
            when (clause) {
                is dveParser.GuardClauseContext -> guard = buildExpr(clause.expr())
                is dveParser.SyncClauseContext -> sync = buildSyncAction(clause.syncAction())
                is dveParser.EffectClauseContext ->
                    effects += clause.effectList().assignment().map { buildAssignment(it) }
            }
        }

        return DveTransition(
            sourceState = ctx.ID(0).text,
            targetState = ctx.ID(1).text,
            guard = guard,
            sync = sync,
            effects = effects,
        )
    }

    private fun buildSyncAction(ctx: dveParser.SyncActionContext): DveSyncAction =
        when (ctx) {
            is dveParser.SyncSendContext ->
                DveSyncAction.Send(
                    channelName = ctx.ID().text,
                    values = ctx.expr().map { buildExpr(it) },
                )
            is dveParser.SyncRecvContext ->
                DveSyncAction.Receive(
                    channelName = ctx.ID().text,
                    variables = ctx.lvalue().map { buildLValue(it) },
                )
            else -> error("Unknown sync action: $ctx")
        }

    private fun buildAssignment(ctx: dveParser.AssignmentContext): DveAssignment =
        DveAssignment(lvalue = buildLValue(ctx.lvalue()), rvalue = buildExpr(ctx.expr()))

    // -------------------------------------------------------------------------
    // LValues
    // -------------------------------------------------------------------------

    private fun buildLValue(ctx: dveParser.LvalueContext): DveLValue =
        when (ctx) {
            is dveParser.SimpleLValueContext ->
                DveLValue.VarLValue(processName = null, varName = ctx.ID().text)
            is dveParser.ArrayLValueContext ->
                DveLValue.ArrayLValue(
                    processName = null,
                    varName = ctx.ID().text,
                    index = buildExpr(ctx.expr()),
                )
            is dveParser.QualLValueContext ->
                DveLValue.VarLValue(
                    processName = ctx.ID(0).text,
                    varName = ctx.ID(1).text,
                )
            is dveParser.QualArrayLValueContext ->
                DveLValue.ArrayLValue(
                    processName = ctx.ID(0).text,
                    varName = ctx.ID(1).text,
                    index = buildExpr(ctx.expr()),
                )
            else -> error("Unknown lvalue: $ctx")
        }

    // -------------------------------------------------------------------------
    // Expressions
    // -------------------------------------------------------------------------

    private fun buildExpr(ctx: dveParser.ExprContext): DveExpression =
        when (ctx) {
            is dveParser.LogOrExprContext ->
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), DveBinaryOp.OR, buildExpr(ctx.expr(1)))
            is dveParser.LogAndExprContext ->
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), DveBinaryOp.AND, buildExpr(ctx.expr(1)))
            is dveParser.BitOrExprContext ->
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), DveBinaryOp.BITOR, buildExpr(ctx.expr(1)))
            is dveParser.BitXorExprContext ->
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), DveBinaryOp.BITXOR, buildExpr(ctx.expr(1)))
            is dveParser.BitAndExprContext ->
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), DveBinaryOp.BITAND, buildExpr(ctx.expr(1)))
            is dveParser.EqExprContext -> {
                val op = if (ctx.EQ2() != null) DveBinaryOp.EQ else DveBinaryOp.NEQ
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), op, buildExpr(ctx.expr(1)))
            }
            is dveParser.RelExprContext -> {
                val op = when {
                    ctx.LT() != null -> DveBinaryOp.LT
                    ctx.LEQ() != null -> DveBinaryOp.LEQ
                    ctx.GT() != null -> DveBinaryOp.GT
                    else -> DveBinaryOp.GEQ
                }
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), op, buildExpr(ctx.expr(1)))
            }
            is dveParser.ShiftExprContext -> {
                val op = if (ctx.SHL() != null) DveBinaryOp.SHL else DveBinaryOp.SHR
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), op, buildExpr(ctx.expr(1)))
            }
            is dveParser.AddExprContext -> {
                val op = if (ctx.PLUS() != null) DveBinaryOp.ADD else DveBinaryOp.SUB
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), op, buildExpr(ctx.expr(1)))
            }
            is dveParser.MulExprContext -> {
                val op = when {
                    ctx.STAR() != null -> DveBinaryOp.MUL
                    ctx.DIV() != null -> DveBinaryOp.DIV
                    else -> DveBinaryOp.MOD
                }
                DveExpression.BinaryExpr(buildExpr(ctx.expr(0)), op, buildExpr(ctx.expr(1)))
            }
            is dveParser.UnaryExprContext -> {
                val op = when {
                    ctx.BANG() != null -> DveUnaryOp.NOT
                    ctx.BITNOT() != null -> DveUnaryOp.BITNOT
                    else -> DveUnaryOp.NEG
                }
                DveExpression.UnaryExpr(op, buildExpr(ctx.expr()))
            }
            is dveParser.AtomExprContext -> buildAtom(ctx.atom())
            else -> error("Unknown expr: $ctx")
        }

    private fun buildAtom(ctx: dveParser.AtomContext): DveExpression =
        when (ctx) {
            is dveParser.IntLitContext ->
                DveExpression.LiteralExpr(ctx.INT_LITERAL().text.toInt())
            is dveParser.SimpleRefContext ->
                DveExpression.VarRefExpr(processName = null, varName = ctx.ID().text)
            is dveParser.ArrayRefContext ->
                DveExpression.ArrayAccessExpr(
                    processName = null,
                    varName = ctx.ID().text,
                    index = buildExpr(ctx.expr()),
                )
            is dveParser.QualifiedRefContext -> resolveQualifiedRef(ctx.ID(0).text, ctx.ID(1).text)
            is dveParser.QualifiedArrayRefContext ->
                DveExpression.ArrayAccessExpr(
                    processName = ctx.ID(0).text,
                    varName = ctx.ID(1).text,
                    index = buildExpr(ctx.expr()),
                )
            is dveParser.ParenExprContext -> buildExpr(ctx.expr())
            else -> error("Unknown atom: $ctx")
        }

    /**
     * Resolves `processName.identifier` to either a [DveExpression.ProcessStateExpr]
     * (if `identifier` is a known state of `processName`) or a [DveExpression.VarRefExpr].
     */
    private fun resolveQualifiedRef(processName: String, identifier: String): DveExpression {
        val states = processStates[processName]
        return if (states != null && identifier in states) {
            DveExpression.ProcessStateExpr(processName = processName, stateName = identifier)
        } else {
            DveExpression.VarRefExpr(processName = processName, varName = identifier)
        }
    }

    // -------------------------------------------------------------------------
    // System declaration
    // -------------------------------------------------------------------------

    private fun buildSystemDecl(ctx: dveParser.SystemDeclContext): DveSystemDecl =
        DveSystemDecl(
            type = if (ctx.systemType().ASYNC() != null) DveSystemType.ASYNC else DveSystemType.SYNC,
            propertyProcessName = ctx.ID()?.text,
        )
}
