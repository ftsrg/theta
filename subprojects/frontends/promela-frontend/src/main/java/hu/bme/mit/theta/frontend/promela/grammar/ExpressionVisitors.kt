package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.PromelaExpression
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

// Used both for rules expr and any_expr
class ExprVisitor : promelaBaseVisitor<PromelaExpression>() {
    override fun visitAny_exprExpr(ctx: promelaParser.Any_exprExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitParenthesesExpr(ctx: promelaParser.ParenthesesExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitAndorExpr(ctx: promelaParser.AndorExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitBinaryAnyExpr(ctx: promelaParser.BinaryAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitUnaryAnyExpr(ctx: promelaParser.UnaryAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitImplAnyExpr(ctx: promelaParser.ImplAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitLenAnyExpr(ctx: promelaParser.LenAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitPollAnyExpr(ctx: promelaParser.PollAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitVarrefAnyExpr(ctx: promelaParser.VarrefAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }

    override fun visitConstAnyExpr(ctx: promelaParser.ConstAnyExprContext?): PromelaExpression {
        throw NotImplementedError()
    }
}