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

fun xcfa(name: String, lambda: XcfaBuilder.() -> Unit): XCFA =
    XcfaBuilder(name).apply(lambda).build()

class VarContext(val builder: XcfaBuilder, private val local: Boolean) {

    infix fun String.type(type: Type): Pair<String, Type> = Pair(this, type)

    infix fun Pair<String, Type>.init(initValue: String): VarDecl<Type> {
        val varDecl = Var(first, second)
        builder.addVar(
            XcfaGlobalVar(varDecl,
                ExpressionWrapper(SimpleScope(SymbolTable()), initValue).instantiate(
                    Env()) as LitExpr<*>,
                local))
        return varDecl
    }
}

fun XcfaProcedureBuilder.lookup(name: String): VarDecl<out Type> =
    getVars().find { it.name.equals(name) } ?: parent.getVars().map { it.wrappedVar }
        .find { it.name.equals(name) } ?: error("Variable $name not found in scope.")

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
        val exprs = expr.map {
            if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                it) else error("Bad type")
        }
        builder.parent.addEntryPoint(builder, exprs)
    }

    infix fun String.type(type: Type): VarDecl<Type> {
        val v = Var(this, type)
        builder.addVar(v)
        return v
    }

    infix fun VarDecl<Type>.direction(direction: ParamDirection): VarDecl<Type> {
        builder.addParam(this, direction)
        return this
    }

    @XcfaDsl
    inner class SequenceLabelContext {

        private val labelList: MutableList<XcfaLabel> = ArrayList()

        infix fun String.assign(to: String): SequenceLabel {
            val lhs: VarDecl<Type> = this@XcfaProcedureBuilderContext.builder.lookup(
                this) as VarDecl<Type>
            val rhs: Expr<Type> = this@XcfaProcedureBuilderContext.builder.parse(to) as Expr<Type>
            val label = StmtLabel(Assign(lhs, rhs), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        infix fun VarDecl<*>.assign(to: String): SequenceLabel {
            val rhs: Expr<Type> = this@XcfaProcedureBuilderContext.builder.parse(to) as Expr<Type>
            val label = StmtLabel(Assign(this as VarDecl<Type>, rhs), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        infix fun String.assign(to: Expr<*>): SequenceLabel {
            val lhs: VarDecl<Type> = this@XcfaProcedureBuilderContext.builder.lookup(
                this) as VarDecl<Type>
            val rhs: Expr<Type> = to as Expr<Type>
            val label = StmtLabel(Assign(lhs, rhs), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        infix fun VarDecl<*>.assign(to: Expr<*>): SequenceLabel {
            val rhs: Expr<Type> = to as Expr<Type>
            val label = StmtLabel(Assign(this as VarDecl<Type>, rhs), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun assume(value: String): SequenceLabel {
            val expr = this@XcfaProcedureBuilderContext.builder.parse(value) as Expr<BoolType>
            val label = StmtLabel(Assume(expr), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun assume(expr: Expr<BoolType>): SequenceLabel {
            val label = StmtLabel(Assume(expr), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun havoc(value: String): SequenceLabel {
            val varDecl = this@XcfaProcedureBuilderContext.builder.lookup(value)
            val label = StmtLabel(Havoc(varDecl), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun havoc(varDecl: VarDecl<*>): SequenceLabel {
            val label = StmtLabel(Havoc(varDecl), metadata = EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        operator fun XcfaProcedureBuilderContext.invoke(vararg expr: Any): SequenceLabel {
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = InvokeLabel(this.builder.name, exprs, EmptyMetaData)
            this@SequenceLabelContext.labelList.add(label)
            return SequenceLabel(this@SequenceLabelContext.labelList)
        }

        operator fun String.invoke(vararg expr: Any): SequenceLabel {
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = InvokeLabel(this, exprs, EmptyMetaData)
            this@SequenceLabelContext.labelList.add(label)
            return SequenceLabel(this@SequenceLabelContext.labelList)
        }

        fun String.start(ctx: XcfaProcedureBuilderContext, vararg expr: Any): SequenceLabel {
            val lhs = this@XcfaProcedureBuilderContext.builder.lookup(this)
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = StartLabel(ctx.builder.name, exprs, lhs, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun VarDecl<*>.start(ctx: XcfaProcedureBuilderContext, vararg expr: Any): SequenceLabel {
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = StartLabel(ctx.builder.name, exprs, this, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun String.start(ctx: String, vararg expr: Any): SequenceLabel {
            val lhs = this@XcfaProcedureBuilderContext.builder.lookup(this)
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = StartLabel(ctx, exprs, lhs, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun VarDecl<*>.start(ctx: String, vararg expr: Any): SequenceLabel {
            val exprs = expr.map {
                if (it is Expr<*>) it else if (it is String) this@XcfaProcedureBuilderContext.builder.parse(
                    it) else error("Bad type")
            }
            val label = StartLabel(ctx, exprs, this, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun String.join(): SequenceLabel {
            val lhs = this@XcfaProcedureBuilderContext.builder.lookup(this)
            val label = JoinLabel(lhs, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun VarDecl<*>.join(): SequenceLabel {
            val label = JoinLabel(this, EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun sequence(lambda: SequenceLabelContext.() -> SequenceLabel): SequenceLabel {
            val innerCtx = this@XcfaProcedureBuilderContext.SequenceLabelContext()
            val label = lambda(innerCtx)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun nondet(lambda: SequenceLabelContext.() -> SequenceLabel): SequenceLabel {
            val innerCtx = this@XcfaProcedureBuilderContext.SequenceLabelContext()
            val label = NondetLabel(lambda(innerCtx).labels.toSet())
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun fence(vararg content: String): SequenceLabel {
            val label = FenceLabel(content.toSet(), EmptyMetaData)
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun nop(): SequenceLabel {
            val label = NopLabel
            labelList.add(label)
            return SequenceLabel(labelList)
        }

        fun skip(): SequenceLabel {
            return SequenceLabel(labelList)
        }
    }

    infix fun String.to(to: String): (lambda: SequenceLabelContext.() -> SequenceLabel) -> XcfaEdge {
        val loc1 = locationLut.getOrElse(this) { XcfaLocation(this) }
        locationLut.putIfAbsent(this, loc1)
        builder.addLoc(loc1)
        val loc2 = locationLut.getOrElse(to) { XcfaLocation(to) }
        locationLut.putIfAbsent(to, loc2)
        builder.addLoc(loc2)
        return { lambda ->
            val edge = XcfaEdge(loc1, loc2, lambda(SequenceLabelContext()))
            builder.addEdge(edge)
            edge
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

fun XcfaBuilder.procedure(name: String, passManager: ProcedurePassManager,
    lambda: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilderContext {
    val builder = XcfaProcedureBuilder(name, passManager)
    builder.parent = this
    val procBuilder = XcfaProcedureBuilderContext(builder).apply(lambda)
    this.addProcedure(procBuilder.builder)
    return procBuilder
}

fun XcfaBuilder.procedure(name: String,
    lambda: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilderContext {
    return procedure(name, ProcedurePassManager(emptyList()), lambda)
}