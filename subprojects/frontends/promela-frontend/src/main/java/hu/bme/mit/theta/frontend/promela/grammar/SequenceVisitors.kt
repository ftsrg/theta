package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.*
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class SequenceVisitor : promelaBaseVisitor<Sequence>() {
    val stepVisitor = StepVisitor()

    override fun visitSequence(ctx: promelaParser.SequenceContext?): Sequence {
        val steps = ctx!!.step().map { it.accept(stepVisitor) }.toList()
    }
}

class StepVisitor(val decl_lstVisitor : Decl_lstVisitor) : promelaBaseVisitor<Step>() {
    val statementVisitor = StatementVisitor()

    override fun visitStmnts(ctx: promelaParser.StmntsContext?): Step {
         return StmntsStep(ctx!!.stmnt().map { it.accept(statementVisitor) }.toList())
    }

    override fun visitDeclLst(ctx: promelaParser.DeclLstContext?): Step {
        return DeclListStep(ctx!!.decl_lst().accept(decl_lstVisitor))
    }

    override fun visitXr(ctx: promelaParser.XrContext?): Step {
        throw NotImplementedError()
    }

    override fun visitXs(ctx: promelaParser.XsContext?): Step {
        throw NotImplementedError()
    }
}