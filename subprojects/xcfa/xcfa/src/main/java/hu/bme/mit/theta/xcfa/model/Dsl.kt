package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.common.dsl.Env
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.grammar.dsl.SimpleScope
import hu.bme.mit.theta.grammar.dsl.expr.ExpressionWrapper
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import kotlin.collections.ArrayList
import kotlin.collections.LinkedHashMap

fun xcfa(name: String, lambda: XcfaBuilder.() -> Unit) : XCFA =
    XcfaBuilder(name).apply(lambda).build()

class VarContext(val builder: XcfaBuilder, private val local: Boolean) {
    infix fun String.type( type: Type ) : Pair<String, Type> = Pair(this, type)

    infix fun Pair<String, Type>.init( initValue: String ): VarDecl<Type> {
        val varDecl = Var(first, second)
        builder.addVar(
            XcfaGlobalVar(  varDecl,
                    ExpressionWrapper(SimpleScope(SymbolTable()), initValue).instantiate(Env()) as LitExpr<*>,
                    local))
        return varDecl
    }
}

fun XcfaProcedureBuilder.lookup(name: String): VarDecl<out Type>? =
    getVars().find { it.name.equals(name) } ?:
    parent.getVars().map { it.wrappedVar }.find { it.name.equals(name) }

data class NamedSymbol(val _name: String) : Symbol {
    override fun getName(): String {
        return _name
    }
}

fun XcfaProcedureBuilder.parse(expr: String): Expr<out Type> {
    val symbolTable = SymbolTable()
    getVars().forEach { symbolTable.add(NamedSymbol(it.name)) }
    parent.getVars().map { it.wrappedVar }.forEach { symbolTable.add(NamedSymbol(it.name)) }
    val env = Env()
    getVars().forEach { env.define(NamedSymbol(it.name), it) }
    parent.getVars().map { it.wrappedVar }.forEach { env.define(NamedSymbol(it.name), it) }

    return ExpressionWrapper(SimpleScope(symbolTable), expr).instantiate(env)
}

@XcfaDsl
class XcfaProcedureBuilderContext(val builder: XcfaProcedureBuilder) {
    private val locationLut: MutableMap<String, XcfaLocation> = LinkedHashMap()
    val init: String = "init"
    val err: String = "err"
    val final: String = "final"

    init {
        builder.createInitLoc()
        builder.createErrorLoc()
        builder.createFinalLoc()
        locationLut[init] = builder.initLoc
        locationLut[err] = builder.errorLoc.get()
        locationLut[final] = builder.finalLoc.get()
    }

    fun start(vararg expr: Any) {
        val exprs = expr.map { if(it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(it) else error("Bad type") }
        builder.parent.addEntryPoint(builder, exprs)
    }

    infix fun String.type( type: Type ) : VarDecl<Type> {
        val v = Var(this, type)
        builder.addVar(v)
        return v
    }

    infix fun VarDecl<Type>.direction( direction: ParamDirection ): VarDecl<Type> {
        builder.addParam(this, direction)
        return this
    }

    @XcfaDsl
    inner class SequenceLabelContext {
        private val labelList: MutableList<XcfaLabel> = ArrayList()

        infix fun String.assign(to: String): XcfaLabel {
            val lhs: VarDecl<Type> = this@XcfaProcedureBuilderContext.builder.lookup(this) as VarDecl<Type>
            val rhs: Expr<Type> = this@XcfaProcedureBuilderContext.builder.parse(to) as Expr<Type>
            val label = StmtLabel(Assign(lhs, rhs), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        infix fun VarDecl<*>.assign(to: String): XcfaLabel {
            val rhs: Expr<Type> = this@XcfaProcedureBuilderContext.builder.parse(to) as Expr<Type>
            val label = StmtLabel(Assign(this as VarDecl<Type>, rhs), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        infix fun String.assign(to: Expr<*>): XcfaLabel {
            val lhs: VarDecl<Type> = this@XcfaProcedureBuilderContext.builder.lookup(this) as VarDecl<Type>
            val rhs: Expr<Type> = to as Expr<Type>
            val label = StmtLabel(Assign(lhs, rhs), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        infix fun VarDecl<*>.assign(to: Expr<*>): XcfaLabel {
            val rhs: Expr<Type> = to as Expr<Type>
            val label = StmtLabel(Assign(this as VarDecl<Type>, rhs), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun assume(value: String): XcfaLabel {
            val expr = this@XcfaProcedureBuilderContext.builder.parse(value) as Expr<BoolType>
            val label = StmtLabel(Assume(expr), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        fun assume(expr: Expr<BoolType>): XcfaLabel {
            val label = StmtLabel(Assume(expr), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun havoc(value: String): XcfaLabel {
            val varDecl = this@XcfaProcedureBuilderContext.builder.lookup(value)
            val label = StmtLabel(Havoc(varDecl), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        fun havoc(varDecl: VarDecl<*>): XcfaLabel {
            val label = StmtLabel(Havoc(varDecl), metadata=EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        operator fun XcfaProcedureBuilderContext.invoke(vararg expr: Any): XcfaLabel {
            val exprs = expr.map { if(it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(it) else error("Bad type") }
            val label = InvokeLabel(this.builder.name, exprs, EmptyMetaData)
            this@SequenceLabelContext.labelList.add(label)
            return SequenceLabel(this@SequenceLabelContext.labelList)
        }

        fun String.start(ctx: XcfaProcedureBuilderContext, vararg expr: Any): XcfaLabel {
            val lhs = this@XcfaProcedureBuilderContext.builder.lookup(this)!!
            val exprs = expr.map { if(it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(it) else error("Bad type") }
            val label = StartLabel(ctx.builder.name, exprs, lhs, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        fun VarDecl<*>.start(ctx: XcfaProcedureBuilderContext, vararg expr: Any): XcfaLabel {
            val exprs = expr.map { if(it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(it) else error("Bad type") }
            val label = StartLabel(ctx.builder.name, exprs, this, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        fun String.join(): XcfaLabel {
            val lhs = this@XcfaProcedureBuilderContext.builder.lookup(this)!!
            val label = JoinLabel(lhs, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
        fun VarDecl<*>.join(): XcfaLabel {
            val label = JoinLabel(this, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }
    }

    infix fun String.to(to: String): (lambda: SequenceLabelContext.() -> XcfaLabel) -> Unit {
        val loc1 = locationLut.getOrElse(this) { XcfaLocation(this) }
        locationLut.putIfAbsent(this, loc1)
        builder.addLoc(loc1)
        val loc2 = locationLut.getOrElse(to) { XcfaLocation(to) }
        locationLut.putIfAbsent(to, loc2)
        builder.addLoc(loc2)
        return { lambda ->
            builder.addEdge(XcfaEdge(loc1, loc2, lambda(SequenceLabelContext())))
        }
    }

}


fun XcfaBuilder.global(lambda: VarContext.() -> Unit) {
    val context = VarContext(this, false)
    context.apply(lambda)
}
fun XcfaBuilder.threadlocal(lambda: VarContext.() -> Unit) {
    val context = VarContext(this, true)
    context.apply(lambda)
}

fun XcfaBuilder.procedure( name: String, lambda: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilderContext {
    val builder = XcfaProcedureBuilder(name, ProcedurePassManager(emptyList()))
    builder.parent = this
    val procBuilder = XcfaProcedureBuilderContext(builder).apply(lambda)
    this.addProcedure(procBuilder.builder)
    return procBuilder
}