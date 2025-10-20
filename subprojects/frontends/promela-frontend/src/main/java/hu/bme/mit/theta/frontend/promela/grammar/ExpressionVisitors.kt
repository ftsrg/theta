package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.frontend.promela.config.PromelaConfiguration
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser
import java.math.BigInteger
import java.util.*

// Used both for rules expr and any_expr
class ExprVisitor(val config : PromelaConfiguration) : promelaBaseVisitor<Expr<*>>()  {
    override fun visitAny_exprExpr(ctx: promelaParser.Any_exprExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitParenthesesExpr(ctx: promelaParser.ParenthesesExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitAndorExpr(ctx: promelaParser.AndorExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitBinaryAnyExpr(ctx: promelaParser.BinaryAnyExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitUnaryAnyExpr(ctx: promelaParser.UnaryAnyExprContext?): Expr<*> {
        val expr = ctx!!.any_expr().accept(this)
        when (ctx.unarop().text) {
            "~" -> {
                @Suppress("UNCHECKED_CAST")
                val negExpr: Expr<*> = BvExprs.Not(expr as Expr<BvType?>?)
            }
            "-" -> {
                val negExpr: Expr<*> = AbstractExprs.Neg(expr)
            }
            "!" -> {
                val negExpr = AbstractExprs.Ite<Type>(
                    AbstractExprs.Eq(
                        expr,
                        CComplexType.getType(expr, parseContext).getNullValue()
                    ), signedInt.getUnitValue(), signedInt.getNullValue()
                )
            }
            else -> {
                throw RuntimeException("Unary operator does not exist")
            }
        }
    }

    override fun visitImplAnyExpr(ctx: promelaParser.ImplAnyExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitLenAnyExpr(ctx: promelaParser.LenAnyExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitPollAnyExpr(ctx: promelaParser.PollAnyExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitVarrefAnyExpr(ctx: promelaParser.VarrefAnyExprContext?): Expr<*> {
        throw NotImplementedError()
    }

    override fun visitConstAnyExpr(ctx: promelaParser.ConstAnyExprContext?): Expr<*> {
        val text = ctx!!.text.lowercase(Locale.getDefault())
        when (text) {
            "false" -> { throw NotImplementedError() }
            "true" -> { throw NotImplementedError() }
            "skip" -> { throw NotImplementedError() }
            else -> {
                val value = BigInteger(text, 10)
                // TODO we do not support Bv arithmetics - disable it on an upper level
                return IntExprs.Int(value)
            }
        }
    }
}