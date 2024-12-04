package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.PromelaExpression
import hu.bme.mit.theta.frontend.promela.model.Variable
import hu.bme.mit.theta.frontend.promela.model.VariableInitialization
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class VariableInitVisitor(val exprVisitor : ExprVisitor) : promelaBaseVisitor<VariableInitialization>() {
    override fun visitIvar(ctx: promelaParser.IvarContext?): VariableInitialization {
        val name = ctx!!.Name().text
        if (ctx.Const() != null) {
            // TODO array init
            throw NotImplementedError()
        }
        if (ctx.ch_init() != null) {
            // TODO ch init
            throw NotImplementedError()
        } else {
            val promelaExpression : PromelaExpression = ctx.any_expr().accept(exprVisitor)
            return VariableInitialization(Variable(name), promelaExpression)
        }
    }
}