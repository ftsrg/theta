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
package hu.bme.mit.theta.grammar.dsl.expr

import com.google.common.base.Preconditions
import com.google.common.collect.ImmutableList
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.dsl.BasicScope
import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.ParamDecl
import hu.bme.mit.theta.core.dsl.DeclSymbol
import hu.bme.mit.theta.core.dsl.ParseException
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.grammar.ThrowingErrorListener
import hu.bme.mit.theta.grammar.dsl.gen.ExprBaseVisitor
import hu.bme.mit.theta.grammar.dsl.gen.ExprLexer
import hu.bme.mit.theta.grammar.dsl.gen.ExprParser
import hu.bme.mit.theta.grammar.dsl.gen.ExprParser.*
import hu.bme.mit.theta.grammar.dsl.type.TypeWrapper
import hu.bme.mit.theta.grammar.textWithWS
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.Token
import java.math.BigInteger
import java.util.*
import java.util.function.Function
import java.util.regex.Pattern
import java.util.stream.Collectors
import java.util.stream.Stream

class ExpressionWrapper(scope: Scope, content: String) {

    private val scope: Scope
    private val context: ExprContext

    init {
        this.scope = Preconditions.checkNotNull(scope)
        val lexer = ExprLexer(CharStreams.fromString(content))
        lexer.addErrorListener(ThrowingErrorListener)
        val parser = ExprParser(CommonTokenStream(lexer))
        parser.errorHandler = BailErrorStrategy()
        this.context = Preconditions.checkNotNull<ExprContext>(parser.expr())
    }

    fun instantiate(env: Env): Expr<out Type> {
        val visitor = ExprCreatorVisitor(scope, env)
        val expr: Expr<*> = context.accept<Expr<*>>(visitor)
        return expr
    }

    private class ExprCreatorVisitor(scope: Scope, env: Env) : ExprBaseVisitor<Expr<out Type>>() {

        private var currentScope: Scope
        private val env: Env

        init {
            currentScope = Preconditions.checkNotNull(scope)
            this.env = Preconditions.checkNotNull(env)
        }

        ////
        private fun push(paramDecls: List<ParamDecl<*>>) {
            val scope = BasicScope(currentScope)
            env.push()
            for (paramDecl in paramDecls) {
                val symbol: Symbol = DeclSymbol.of(paramDecl)
                scope.declare(symbol)
                env.define(symbol, paramDecl)
            }
            currentScope = scope
        }

        private fun pop() {
            Preconditions.checkState(currentScope.enclosingScope().isPresent,
                "Enclosing scope is not present.")
            currentScope = currentScope.enclosingScope().get()
            env.pop()
        }

        ////
        override fun visitFuncLitExpr(ctx: FuncLitExprContext): Expr<out Type> {
            return if (ctx.result != null) {
                val param = Decls.Param(ctx.param.name.text,
                    TypeWrapper(ctx.param.type().textWithWS()).instantiate())
                push(listOf(param))
                val result = ctx.result.accept<Expr<*>>(this) as Expr<Type>
                pop()
                FuncExprs.Func(param, result)
            } else {
                visitChildren(ctx)
            }
        }

        private fun createParamList(ctx: DeclListContext): List<ParamDecl<*>> {
            return if (ctx.decls == null) {
                emptyList()
            } else {
                ctx.decls.stream()
                    .map { d: DeclContext ->
                        Decls.Param(d.name.getText(),
                            TypeWrapper(d.ttype.textWithWS()).instantiate())
                    }.collect(Collectors.toList())
            }
        }

        ////
        override fun visitIteExpr(ctx: IteExprContext): Expr<out Type> {
            return if (ctx.cond != null) {
                val cond: Expr<BoolType> = TypeUtils.cast(ctx.cond.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                val then: Expr<*> = ctx.then.accept<Expr<*>>(this)
                val elze: Expr<*> = ctx.elze.accept<Expr<*>>(this)
                AbstractExprs.Ite<Type>(cond, then, elze)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitIffExpr(ctx: IffExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp: Expr<BoolType> = TypeUtils.cast(ctx.leftOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                val rightOp: Expr<BoolType> = TypeUtils.cast(ctx.rightOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                BoolExprs.Iff(leftOp, rightOp)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitImplyExpr(ctx: ImplyExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp: Expr<BoolType> = TypeUtils.cast(ctx.leftOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                val rightOp: Expr<BoolType> = TypeUtils.cast(ctx.rightOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                BoolExprs.Imply(leftOp, rightOp)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitForallExpr(ctx: ForallExprContext): Expr<out Type> {
            return if (ctx.paramDecls != null) {
                val paramDecls = createParamList(ctx.paramDecls)
                push(paramDecls)
                val op: Expr<BoolType> = TypeUtils.cast(ctx.op.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                pop()
                BoolExprs.Forall(paramDecls, op)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitExistsExpr(ctx: ExistsExprContext): Expr<out Type> {
            return if (ctx.paramDecls != null) {
                val paramDecls = createParamList(ctx.paramDecls)
                push(paramDecls)
                val op: Expr<BoolType> = TypeUtils.cast(ctx.op.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                pop()
                BoolExprs.Exists(paramDecls, op)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitOrExpr(ctx: OrExprContext): Expr<out Type> {
            return if (ctx.ops.size >= 1) {
                val opStream: Stream<Expr<BoolType>> = ctx.ops.stream()
                    .map({ op: ExprContext ->
                        TypeUtils.cast(op.accept<Expr<*>>(this), BoolExprs.Bool())
                    })
                val ops: Collection<Expr<BoolType>> = opStream.collect(Collectors.toList())
                BoolExprs.Or(ops)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitXorExpr(ctx: XorExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp: Expr<BoolType> = TypeUtils.cast(ctx.leftOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                val rightOp: Expr<BoolType> = TypeUtils.cast(ctx.rightOp.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                BoolExprs.Xor(leftOp, rightOp)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitAndExpr(ctx: AndExprContext): Expr<out Type> {
            return if (ctx.ops.size >= 1) {
                val opStream: Stream<Expr<BoolType>> = ctx.ops.stream()
                    .map({ op: ExprContext ->
                        TypeUtils.cast(op.accept<Expr<*>>(this), BoolExprs.Bool())
                    })
                val ops: Collection<Expr<BoolType>> = opStream.collect(Collectors.toList())
                BoolExprs.And(ops)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitNotExpr(ctx: NotExprContext): Expr<out Type> {
            return if (ctx.op != null) {
                val op: Expr<BoolType> = TypeUtils.cast(ctx.op.accept<Expr<*>>(this),
                    BoolExprs.Bool())
                BoolExprs.Not(op)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitEqualityExpr(ctx: EqualityExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp: Expr<*> = ctx.leftOp.accept<Expr<*>>(this)
                val rightOp: Expr<*> = ctx.rightOp.accept<Expr<*>>(this)
                when (ctx.oper.getType()) {
                    EQ -> AbstractExprs.Eq(leftOp, rightOp)
                    NEQ -> AbstractExprs.Neq(leftOp, rightOp)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitRelationExpr(ctx: RelationExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp: Expr<*> = ctx.leftOp.accept<Expr<*>>(this)
                val rightOp: Expr<*> = ctx.rightOp.accept<Expr<*>>(this)
                when (ctx.oper.getType()) {
                    LT -> AbstractExprs.Lt(leftOp, rightOp)
                    LEQ -> AbstractExprs.Leq(leftOp, rightOp)
                    GT -> AbstractExprs.Gt(leftOp, rightOp)
                    GEQ -> AbstractExprs.Geq(leftOp, rightOp)
                    BV_ULT -> BvExprs.ULt(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_ULE -> BvExprs.ULeq(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_UGT -> BvExprs.UGt(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_UGE -> BvExprs.UGeq(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_SLT -> BvExprs.SLt(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_SLE -> BvExprs.SLeq(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_SGT -> BvExprs.SGt(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    BV_SGE -> BvExprs.SGeq(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitFpFuncExpr(ctx: FpFuncExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp = ctx.leftOp.accept<Expr<*>>(this) as Expr<FpType>
                val rightOp = ctx.rightOp.accept<Expr<*>>(this) as Expr<FpType>
                when (ctx.oper.getType()) {
                    FPMAX -> FpExprs.Max(leftOp, rightOp)
                    FPMIN -> FpExprs.Min(leftOp, rightOp)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        ////
        override fun visitBitwiseOrExpr(ctx: BitwiseOrExprContext): Expr<out Type> {
            return if (ctx.oper != null) {
                val opStream: Stream<Expr<(BvType)>> = ctx.ops.stream()
                    .map { op: ExprContext -> op.accept<Expr<*>>(this) as Expr<BvType> }
                val ops: MutableList<Expr<BvType>> = opStream.collect(Collectors.toList())
                when (ctx.oper.type) {
                    BV_OR -> BvExprs.Or(ops)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitBitwiseXorExpr(ctx: BitwiseXorExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp = TypeUtils.castBv(ctx.leftOp.accept<Expr<*>>(this))
                val rightOp = TypeUtils.castBv(ctx.rightOp.accept<Expr<*>>(this))
                when (ctx.oper.getType()) {
                    BV_XOR -> BvExprs.Xor(java.util.List.of(leftOp, rightOp))
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitBitwiseAndExpr(ctx: BitwiseAndExprContext): Expr<out Type> {
            return if (ctx.oper != null) {
                val opStream: Stream<Expr<(BvType)>> = ctx.ops.stream()
                    .map { op: ExprContext -> op.accept<Expr<*>>(this) as Expr<BvType> }
                val ops: MutableList<Expr<BvType>> = opStream.collect(Collectors.toList())
                when (ctx.oper.type) {
                    BV_AND -> BvExprs.And(ops)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitBitwiseShiftExpr(ctx: BitwiseShiftExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val leftOp = TypeUtils.castBv(ctx.leftOp.accept<Expr<*>>(this))
                val rightOp = TypeUtils.castBv(ctx.rightOp.accept<Expr<*>>(this))
                when (ctx.oper.getType()) {
                    BV_SHL -> BvExprs.ShiftLeft(leftOp, rightOp)
                    BV_ASHR -> BvExprs.ArithShiftRight(leftOp, rightOp)
                    BV_LSHR -> BvExprs.LogicShiftRight(leftOp, rightOp)
                    BV_ROL -> BvExprs.RotateLeft(leftOp, rightOp)
                    BV_ROR -> BvExprs.RotateRight(leftOp, rightOp)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        ////
        override fun visitAdditiveExpr(ctx: AdditiveExprContext): Expr<out Type> {
            return if (ctx.ops.size >= 1) {
                val opStream: Stream<Expr<*>> = ctx.ops.stream()
                    .map(Function { op: ExprContext -> op.accept<Expr<*>>(this) })
                val ops = opStream.collect(Collectors.toList())
                val opsHead = ops[0]
                val opsTail = ops.subList(1, ops.size)
                createAdditiveExpr(opsHead, opsTail, ctx.oper, ctx)
            } else {
                visitChildren(ctx)
            }
        }

        private fun createAdditiveExpr(opsHead: Expr<*>, opsTail: List<Expr<*>>,
            oper: Token, ctx: AdditiveExprContext): Expr<out Type> {
            return if (opsTail.isEmpty()) {
                opsHead
            } else {
                val newOpsHead = opsTail[0]
                val newOpsTail = opsTail.subList(1, opsTail.size)
                val subExpr = createAdditiveSubExpr(opsHead, newOpsHead, oper, ctx)
                createAdditiveExpr(subExpr, newOpsTail, oper, ctx)
            }
        }

        private fun createAdditiveSubExpr(leftOp: Expr<*>, rightOp: Expr<*>, oper: Token,
            ctx: AdditiveExprContext): Expr<out Type> {
            return when (oper.type) {
                PLUS -> createAddExpr(leftOp, rightOp)
                MINUS -> createSubExpr(leftOp, rightOp)
                BV_ADD -> createBvAddExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                BV_SUB -> createBvSubExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                FPADD -> FpExprs.Add(getRoundingMode(ctx.oper.text),
                    java.util.List.of(TypeUtils.castFp(leftOp), TypeUtils.castFp(rightOp)))

                FPSUB -> FpExprs.Sub(getRoundingMode(ctx.oper.text), TypeUtils.castFp(leftOp),
                    TypeUtils.castFp(rightOp))

                else -> throw ParseException(ctx, "Unknown operator '" + oper.text + "'")
            }
        }

        private fun createAddExpr(leftOp: Expr<*>, rightOp: Expr<*>): AddExpr<*> {
            return if (leftOp is AddExpr<*>) {
                val ops: List<Expr<*>> = ImmutableList.builder<Expr<*>>().addAll(leftOp.ops)
                    .add(rightOp)
                    .build()
                AbstractExprs.Add(ops)
            } else {
                AbstractExprs.Add(leftOp, rightOp)
            }
        }

        private fun createSubExpr(leftOp: Expr<*>, rightOp: Expr<*>): SubExpr<*> {
            return AbstractExprs.Sub(leftOp, rightOp)
        }

        private fun createBvAddExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvAddExpr {
            return if (leftOp is BvAddExpr) {
                val ops: List<Expr<BvType>> = ImmutableList.builder<Expr<BvType>>()
                    .addAll(leftOp.ops).add(rightOp)
                    .build()
                BvExprs.Add(ops)
            } else {
                BvExprs.Add(Arrays.asList(leftOp, rightOp))
            }
        }

        private fun createBvSubExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvSubExpr {
            return BvExprs.Sub(leftOp, rightOp)
        }

        ////
        override fun visitMultiplicativeExpr(ctx: MultiplicativeExprContext): Expr<out Type> {
            return if (ctx.ops.size >= 1) {
                val opStream: Stream<Expr<*>> = ctx.ops.stream()
                    .map(Function { op: ExprContext -> op.accept<Expr<*>>(this) })
                val ops = opStream.collect(Collectors.toList())
                val opsHead = ops[0]
                val opsTail = ops.subList(1, ops.size)
                createMutliplicativeExpr(opsHead, opsTail, ctx.oper, ctx)
            } else {
                visitChildren(ctx)
            }
        }

        private fun createMutliplicativeExpr(opsHead: Expr<*>, opsTail: List<Expr<*>>,
            oper: Token, ctx: MultiplicativeExprContext): Expr<out Type> {
            return if (opsTail.isEmpty()) {
                opsHead
            } else {
                val newOpsHead = opsTail[0]
                val newOpsTail = opsTail.subList(1, opsTail.size)
                val subExpr = createMultiplicativeSubExpr(opsHead, newOpsHead, oper, ctx)
                createMutliplicativeExpr(subExpr, newOpsTail, oper, ctx)
            }
        }

        private fun createMultiplicativeSubExpr(leftOp: Expr<*>, rightOp: Expr<*>, oper: Token,
            ctx: MultiplicativeExprContext): Expr<out Type> {
            return when (oper.type) {
                MUL -> createMulExpr(leftOp, rightOp)
                BV_MUL -> createBvMulExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                DIV -> createDivExpr(leftOp, rightOp)
                BV_UDIV -> createBvUDivExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                BV_SDIV -> createBvSDivExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                MOD -> createModExpr(leftOp, rightOp)
                BV_SMOD -> createBvSModExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                REM -> createRemExpr(leftOp, rightOp)
                BV_UREM -> createBvURemExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                BV_SREM -> createBvSRemExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                FPREM -> FpExprs.Rem(leftOp as Expr<FpType?>, rightOp as Expr<FpType?>)
                FPMUL -> FpExprs.Mul(getRoundingMode(ctx.oper.text),
                    java.util.List.of(leftOp as Expr<FpType>, rightOp as Expr<FpType>))

                FPDIV -> FpExprs.Div(getRoundingMode(ctx.oper.text), leftOp as Expr<FpType?>,
                    rightOp as Expr<FpType?>)

                else -> throw ParseException(ctx, "Unknown operator '" + oper.text + "'")
            }
        }

        private fun createMulExpr(leftOp: Expr<*>, rightOp: Expr<*>): MulExpr<*> {
            return if (leftOp is MulExpr<*>) {
                val ops: List<Expr<*>> = ImmutableList.builder<Expr<*>>().addAll(leftOp.ops)
                    .add(rightOp)
                    .build()
                AbstractExprs.Mul(ops)
            } else {
                AbstractExprs.Mul(leftOp, rightOp)
            }
        }

        private fun createBvMulExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvMulExpr {
            return if (leftOp is BvMulExpr) {
                val ops: List<Expr<BvType>> = ImmutableList.builder<Expr<BvType>>()
                    .addAll(leftOp.ops).add(rightOp)
                    .build()
                BvExprs.Mul(ops)
            } else {
                BvExprs.Mul(Arrays.asList(leftOp, rightOp))
            }
        }

        private fun createDivExpr(leftOp: Expr<*>, rightOp: Expr<*>): DivExpr<*> {
            return AbstractExprs.Div(leftOp, rightOp)
        }

        private fun createBvUDivExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvUDivExpr {
            return BvExprs.UDiv(leftOp, rightOp)
        }

        private fun createBvSDivExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvSDivExpr {
            return BvExprs.SDiv(leftOp, rightOp)
        }

        private fun createModExpr(uncastLeftOp: Expr<*>, uncastRightOp: Expr<*>): ModExpr<*> {
            return AbstractExprs.Mod(uncastLeftOp, uncastRightOp)
        }

        private fun createBvSModExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvSModExpr {
            return BvExprs.SMod(leftOp, rightOp)
        }

        private fun createRemExpr(uncastLeftOp: Expr<*>, uncastRightOp: Expr<*>): RemExpr<*> {
            return AbstractExprs.Rem(uncastLeftOp, uncastRightOp)
        }

        private fun createBvURemExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvURemExpr {
            return BvExprs.URem(leftOp, rightOp)
        }

        private fun createBvSRemExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvSRemExpr {
            return BvExprs.SRem(leftOp, rightOp)
        }

        ////
        override fun visitBvConcatExpr(ctx: BvConcatExprContext): Expr<out Type> {
            return if (ctx.ops.size >= 1) {
                val opStream: Stream<Expr<*>> = ctx.ops.stream()
                    .map(Function { op: ExprContext -> op.accept<Expr<*>>(this) })
                val ops = opStream.collect(Collectors.toList())
                val opsHead = ops[0]
                val opsTail = ops.subList(1, ops.size)
                createConcatExpr(opsHead, opsTail, ctx.oper)
            } else {
                visitChildren(ctx)
            }
        }

        private fun createConcatExpr(opsHead: Expr<*>, opsTail: List<Expr<*>>,
            oper: Token): Expr<out Type> {
            return if (opsTail.isEmpty()) {
                opsHead
            } else {
                val newOpsHead = opsTail[0]
                val newOpsTail = opsTail.subList(1, opsTail.size)
                val subExpr = createConcatSubExpr(opsHead, newOpsHead, oper)
                createConcatExpr(subExpr, newOpsTail, oper)
            }
        }

        private fun createConcatSubExpr(leftOp: Expr<*>, rightOp: Expr<*>,
            oper: Token): Expr<out Type> {
            return when (oper.type) {
                BV_CONCAT -> createBvConcatExpr(TypeUtils.castBv(leftOp), TypeUtils.castBv(rightOp))
                else -> throw AssertionError()
            }
        }

        private fun createBvConcatExpr(leftOp: Expr<BvType>, rightOp: Expr<BvType>): BvConcatExpr {
            return if (leftOp is BvConcatExpr) {
                val ops: List<Expr<BvType>> = ImmutableList.builder<Expr<BvType>>()
                    .addAll(leftOp.ops).add(rightOp)
                    .build()
                BvExprs.Concat(ops)
            } else {
                BvExprs.Concat(Arrays.asList(leftOp, rightOp))
            }
        }

        override fun visitBvExtendExpr(ctx: BvExtendExprContext): Expr<out Type> {
            return if (ctx.rightOp != null) {
                val extendType = BvExprs.BvType(ctx.rightOp.size.getText().toInt())
                when (ctx.oper.getType()) {
                    BV_ZERO_EXTEND -> BvExprs.ZExt(
                        TypeUtils.castBv(ctx.leftOp.accept<Expr<*>>(this)), extendType)

                    BV_SIGN_EXTEND -> BvExprs.SExt(
                        TypeUtils.castBv(ctx.leftOp.accept<Expr<*>>(this)), extendType)

                    else -> throw AssertionError()
                }
            } else {
                visitChildren(ctx)
            }
        }

        ////
        override fun visitUnaryExpr(ctx: UnaryExprContext): Expr<out Type> {
            return if (ctx.op != null) {
                val op: Expr<*> = ctx.op.accept<Expr<*>>(this)
                when (ctx.oper.getType()) {
                    PLUS -> AbstractExprs.Pos(op)
                    MINUS -> AbstractExprs.Neg(op)
                    FP_ABS -> FpExprs.Abs(op as Expr<FpType?>)
                    FP_IS_INF -> FpExprs.IsInfinite(op as Expr<FpType?>)
                    FP_IS_NAN -> FpExprs.IsNan(op as Expr<FpType?>)
                    FPROUNDTOINT -> FpExprs.RoundToIntegral(getRoundingMode(ctx.oper.text),
                        op as Expr<FpType?>)

                    FPSQRT -> FpExprs.Sqrt(getRoundingMode(ctx.oper.text), op as Expr<FpType?>)
                    FPTOFP -> FpExprs.ToFp(getRoundingMode(ctx.oper.text), op as Expr<FpType?>,
                        getExp(ctx.oper.getText()), getSignificand(ctx.oper.getText()))

                    FPTOBV -> FpExprs.ToBv(getRoundingMode(ctx.oper.text), op as Expr<FpType?>,
                        getBvSize(ctx.oper.getText()), isSignedBv(ctx.oper.getText()))

                    FP_FROM_BV -> FpExprs.FromBv(getRoundingMode(ctx.oper.text),
                        op as Expr<BvType?>,
                        FpType.of(getExp(ctx.oper.getText()), getSignificand(ctx.oper.getText())),
                        isSignedFp(ctx.oper.getText()))

                    FPNEG -> FpExprs.Neg(op as Expr<FpType?>)
                    FPPOS -> FpExprs.Pos(op as Expr<FpType?>)
                    BV_POS -> BvExprs.Pos(op as Expr<BvType>)
                    BV_NEG -> BvExprs.Neg(op as Expr<BvType>)
                    else -> throw ParseException(ctx, "Unknown operator")
                }
            } else {
                visitChildren(ctx)
            }
        }

        private fun isSignedFp(text: String): Boolean {
            val pattern = Pattern.compile("\\[([us])]")
            val matcher = pattern.matcher(text)
            return if (matcher.find()) {
                matcher.group(1) != "u"
            } else false
        }

        private fun isSignedBv(text: String): Boolean {
            val pattern = Pattern.compile("\\[[0-9]*'([us])]")
            val matcher = pattern.matcher(text)
            return if (matcher.find()) {
                matcher.group(1) != "u"
            } else throw RuntimeException("Signedness not well formed in bv type!")
        }

        private fun getBvSize(text: String): Int {
            val pattern = Pattern.compile("\\[([0-9]*)'[us]]")
            val matcher = pattern.matcher(text)
            return if (matcher.find()) {
                matcher.group(1).toInt()
            } else throw RuntimeException("Size not well formed in bv type!")
        }

        private fun getExp(text: String): Int {
            val pattern = Pattern.compile("\\[([0-9]*),([0-9]*)]")
            val matcher = pattern.matcher(text)
            return if (matcher.find()) {
                matcher.group(1).toInt()
            } else throw RuntimeException("Exponent not well formed in fp type!")
        }

        private fun getSignificand(text: String): Int {
            val pattern = Pattern.compile("\\[([0-9]*),([0-9]*)]")
            val matcher = pattern.matcher(text)
            return if (matcher.find()) {
                matcher.group(2).toInt()
            } else throw RuntimeException("Significand not well formed in fp type!")
        }

        private fun getRoundingMode(text: String): FpRoundingMode {
            val pattern = Pattern.compile("\\[((RNA)|(RNE)|(RTP)|(RTN)|(RTZ))]")
            val matcher = pattern.matcher(text)
            if (matcher.find()) {
                return FpRoundingMode.valueOf(matcher.group(1).uppercase())
            }
            return FpRoundingMode.getDefaultRoundingMode()
        }

        override fun visitBitwiseNotExpr(ctx: BitwiseNotExprContext): Expr<out Type> {
            return if (ctx.op != null) {
                val op = TypeUtils.castBv(ctx.op.accept<Expr<*>>(this))
                BvExprs.Not(op)
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitFunctionCall(ctx: FunctionCallContext): Expr<out Type> {
            return if (ctx.op != null) {
                throw UnsupportedOperationException("Function application not yet supported.")
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitArrayRead(ctx: ArrayReadContext): Expr<out Type> {
            return if (ctx.array != null) {
                ArrayReadExpr.create<Type, Type>(
                    ctx.array.accept(this),
                    ctx.index.accept(this))
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitArrayWrite(ctx: ArrayWriteContext): Expr<out Type> {
            return if (ctx.array != null) {
                ArrayWriteExpr.create<Type, Type>(
                    ctx.array.accept(this),
                    ctx.index.accept(this),
                    ctx.elem.accept(this))
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitPrimeExpr(ctx: PrimeExprContext): Expr<out Type> {
            return if (ctx.op != null) {
                Exprs.Prime(ctx.op.accept(this))
            } else {
                visitChildren(ctx)
            }
        }

        override fun visitBvExtract(ctx: BvExtractContext): Expr<out Type> {
            return if (ctx.op != null) {
                val op = ctx.op.accept(this)
                val bitvec = TypeUtils.castBv(op)
                return BvExprs.Extract(bitvec, Int(ctx.from.getText()),
                    IntExprs.Int(ctx.until.getText()))
            } else {
                visitChildren(ctx)
            }
        }

        ////
        override fun visitTrueExpr(ctx: TrueExprContext): TrueExpr {
            return BoolExprs.True()
        }

        override fun visitFalseExpr(ctx: FalseExprContext): FalseExpr {
            return BoolExprs.False()
        }

        override fun visitIntLitExpr(ctx: IntLitExprContext): IntLitExpr {
            val value: BigInteger = BigInteger(ctx.text)
            return IntExprs.Int(value)
        }

        override fun visitRatLitExpr(ctx: RatLitExprContext): RatLitExpr {
            val num = BigInteger(ctx.num.text)
            val denom = BigInteger(ctx.denom.getText())
            return RatExprs.Rat(num, denom)
        }

        override fun visitFpLitExpr(ctx: FpLitExprContext): Expr<out Type> {
            val hidden = ctx.bvLitExpr(0).accept<Expr<*>>(this) as BvLitExpr
            val exponent = ctx.bvLitExpr(1).accept<Expr<*>>(this) as BvLitExpr
            val significand = ctx.bvLitExpr(2).accept<Expr<*>>(this) as BvLitExpr
            return FpLitExpr.of(hidden == Bv(BooleanArray(1) { true }), exponent, significand)
        }

        override fun visitArrLitExpr(ctx: ArrLitExprContext): Expr<out Type> {
            Preconditions.checkNotNull<ExprContext>(ctx.elseExpr)
            val indexType = if (ctx.indexExpr.size > 0) ctx.indexExpr[0].accept(
                this).type else Int()
            val elseElem = ctx.elseExpr.accept(this)
            val valueType = elseElem.type
            val elems = ctx.indexExpr.mapIndexed { idx, it ->
                Tuple2.of(it.accept(this), ctx.valueExpr[idx].accept(this))
            }
            return ExprUtils.simplify(ArrayInitExpr.create<Type, Type>(elems, elseElem,
                ArrayType.of(indexType, valueType)))
        }

        override fun visitBvLitExpr(ctx: BvLitExprContext): Expr<out Type> {
            val sizeAndContent: Array<String> = ctx.bv.getText().split("['#]".toRegex())
                .dropLastWhile { it.isEmpty() }.toTypedArray()
            val content = if (sizeAndContent.size == 2) sizeAndContent[1] else sizeAndContent[0]
            val value: BooleanArray = if (content.startsWith("b")) {
                decodeBinaryBvContent(content.substring(1))
            } else if (content.startsWith("d")) {
                check(
                    sizeAndContent.size == 2) { "Decimal value is only parseable if size is given." }
                decodeDecimalBvContent(content.substring(1), sizeAndContent[0].toInt())
            } else if (content.startsWith("x")) {
                decodeHexadecimalBvContent(content.substring(1))
            } else {
                throw ParseException(ctx, "Invalid bitvector literal")
            }
            val bvValue = BooleanArray(value.size)
            for (i in value.indices) {
                bvValue[value.size - 1 - i] = value[value.size - 1 - i]
            }
            return BvExprs.Bv(bvValue)
        }

        private fun decodeBinaryBvContent(lit: String): BooleanArray {
            val value = BooleanArray(lit.length)
            for (i in 0 until lit.length) {
                when (lit.toCharArray()[i]) {
                    '0' -> value[i] = false
                    '1' -> value[i] = true
                    else -> throw IllegalArgumentException(
                        "Binary literal can contain only 0 and 1")
                }
            }
            return value
        }

        private fun decodeDecimalBvContent(lit: String, size: Int): BooleanArray {
            var value = BigInteger(lit)
            Preconditions.checkArgument(
                value.compareTo(
                    BigInteger.TWO.pow(size - 1).multiply(BigInteger.valueOf(-1))) >= 0 &&
                    value.compareTo(BigInteger.TWO.pow(size)) < 0,
                "Decimal literal is not in range"
            )
            if (value.compareTo(BigInteger.ZERO) < 0) {
                value = value.add(BigInteger.TWO.pow(size))
            }
            return decodeBinaryBvContent(value.toString(2))
        }

        private fun decodeHexadecimalBvContent(lit: String): BooleanArray {
            val builder = StringBuilder()
            for (i in 0 until lit.length) {
                when (lit.toCharArray()[i].lowercaseChar()) {
                    '0' -> builder.append("0000")
                    '1' -> builder.append("0001")
                    '2' -> builder.append("0010")
                    '3' -> builder.append("0011")
                    '4' -> builder.append("0100")
                    '5' -> builder.append("0101")
                    '6' -> builder.append("0110")
                    '7' -> builder.append("0111")
                    '8' -> builder.append("1000")
                    '9' -> builder.append("1001")
                    'a' -> builder.append("1010")
                    'b' -> builder.append("1011")
                    'c' -> builder.append("1100")
                    'd' -> builder.append("1101")
                    'e' -> builder.append("1110")
                    'f' -> builder.append("1111")
                    else -> throw IllegalArgumentException("Invalid hexadecimal character")
                }
            }
            return decodeBinaryBvContent(builder.toString())
        }

        override fun visitIdExpr(ctx: IdExprContext): RefExpr<*> {
            val optSymbol = currentScope.resolve(ctx.id.getText())
            if (optSymbol.isEmpty) {
                throw ParseException(ctx,
                    "Identifier '" + ctx.id.getText() + "' cannot be resolved")
            }
            val symbol = optSymbol.get()
            val decl = env.eval(symbol) as Decl<*>
            return decl.ref
        }

        override fun visitParenExpr(ctx: ParenExprContext): Expr<out Type> {
            return ctx.op.accept<Expr<*>>(this)
        }
    }
}