package hu.bme.mit.theta.frontend.promela.grammar

import hu.bme.mit.theta.frontend.promela.model.*
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaBaseVisitor
import hu.bme.mit.theta.promela.frontend.dsl.gen.promelaParser

class SpecVisitor : promelaBaseVisitor<Spec>() {
    override fun visitSpec(ctx: promelaParser.SpecContext): Spec {
        return Spec(ctx.module().map { ModuleVisitor().visitModule(it) })
    }
}

// TODO add fixed single visitors for each visitor class used
class ModuleVisitor : promelaBaseVisitor<Module>() {
    override fun visitModule(ctx: promelaParser.ModuleContext): Module {
        return when {
            ctx.proctype() != null -> ctx.proctype().accept(ProctypeVisitor())
            ctx.init() != null -> InitVisitor().visitInit(ctx.init())
            ctx.never() != null -> visitNever(ctx.never()) // TODO add accept and classes
            ctx.trace() != null -> visitTrace(ctx.trace())
            ctx.utype() != null -> visitUtype(ctx.utype())
            ctx.mtype() != null -> visitMtype(ctx.mtype())
            ctx.decl_lst() != null -> visitDecl_lst(ctx.decl_lst())
            else -> throw RuntimeException("Module should not have any other subclasses")
        }
    }
}

class ProctypeVisitor : promelaBaseVisitor<Proctype>() {
    override fun visitProctype(ctx: promelaParser.ProctypeContext): Proctype {
        val active = ctx.active()?.Const()?.text
        val name = ctx.Name().text
        val declList = ctx.decl_lst()?.accept(Decl_lstVisitor())
        val priority = ctx.priority()?.Const()?.text
        val enabler = ctx.enabler()?.expr()?.text
        val sequence = ctx.sequence().step().map { it.accept() }
        return Proctype(active, name, declList, priority, enabler, sequence)
    }
}

class InitVisitor : promelaBaseVisitor<Init>() {
    override fun visitInit(ctx: promelaParser.InitContext): Init {
        val priority = ctx.priority()?.Const()?.text
        val sequence = ctx.sequence().step().map { it.accept(this) }
        return Init(priority, sequence)
    }
}

class NeverVisitor : promelaBaseVisitor<Never>() {
    override fun visitNever(ctx: promelaParser.NeverContext): Never {
        val sequence = ctx.sequence().step().map { it.accept(this) }
        return Never(sequence)
    }
}

class TraceVisitor : promelaBaseVisitor<Trace>() {
    override fun visitTrace(ctx: promelaParser.TraceContext): Trace {
        val sequence = ctx.sequence().step().map { it.accept(this) }
        return Trace(sequence)
    }
}

class UtypeVisitor : promelaBaseVisitor<Utype>() {
    override fun visitUtype(ctx: promelaParser.UtypeContext): Utype {
        val name = ctx.Name().text
        val declList = ctx.decl_lst().accept(this) as DeclList
        return Utype(name, declList)
    }
}

class MtypeVisitor : promelaBaseVisitor<Mtype>() {
    override fun visitMtype(ctx: promelaParser.MtypeContext): Mtype {
        val names = ctx.Name().map { it.text }
        return Mtype(names)
    }
}

class Decl_lstVisitor : promelaBaseVisitor<DeclList>() {
    val oneDeclVisitor = OneDeclVisitor()
    override fun visitDecl_lst(ctx: promelaParser.Decl_lstContext): DeclList {
        val declarations = ctx.one_decl().map { it.accept(oneDeclVisitor) }

    }
}

class OneDeclVisitor(val exprVisitor : ExprVisitor) : promelaBaseVisitor<OneDecl>() {
    val variableInitVisitor = VariableInitVisitor(exprVisitor)
    override fun visitOne_decl(ctx: promelaParser.One_declContext?): OneDecl {
        ctx!!.typename()
        ctx.ivar().map { it.accept(variableInitVisitor) }
    }
}