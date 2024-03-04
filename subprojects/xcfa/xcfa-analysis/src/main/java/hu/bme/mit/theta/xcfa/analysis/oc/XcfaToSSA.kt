package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.core.decl.IndexedVarDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager

internal val Expr<*>.vars get() = ExprUtils.getVars(this)

fun XCFA.toSSA(): XCFA {
    val passManager = ProcedurePassManager(listOf(SSAPass()))
    val copy: XcfaProcedureBuilder.() -> XcfaProcedureBuilder = {
        XcfaProcedureBuilder(
            name = name,
            manager = passManager,
            params = getParams().toMutableList(),
            vars = getVars().toMutableSet(),
            locs = getLocs().toMutableSet(),
            edges = getEdges().toMutableSet(),
            metaData = metaData.toMutableMap()
        ).also { it.copyMetaLocs(this) }
    }

    val builder = XcfaBuilder("${name}_SSA", vars.toMutableSet())
    procedureBuilders.forEach { builder.addProcedure(it.copy()) }
    initProcedureBuilders.forEach { (proc, params) ->
        val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
        builder.addEntryPoint(initProc, params)
    }
    return builder.build()
}

class SSAPass : ProcedurePass {

    private var indexing: VarIndexing = VarIndexingFactory.indexing(0)

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.unfold()))
        }
        return builder
    }

    private fun XcfaLabel.unfold(): XcfaLabel {
        return when (this) {
            is StmtLabel -> {
                when (val stmt = this.stmt) {
                    is AssignStmt<*> -> StmtLabel(stmt.toSSA(), choiceType, metadata)
                    is AssumeStmt -> StmtLabel(stmt.toSSA(), choiceType, metadata)
                    is HavocStmt<*> -> StmtLabel(stmt.toSSA(), choiceType, metadata)
                    else -> error("Unsupported statement at SSA conversion: $stmt")
                }
            }

            is StartLabel -> StartLabel(name, params.map { it.unfold() }, pidVar.newIndexed(), metadata, tempLookup)
            is JoinLabel -> JoinLabel(pidVar.newIndexed(), metadata)
            is SequenceLabel -> SequenceLabel(labels.map { it.unfold() }, metadata)
            is NopLabel, is FenceLabel -> this
            else -> error("Unsupported label at SSA conversion: $this")
        }
    }

    private fun <T : Type> Expr<T>.unfold(): Expr<T> {
        if (this is RefExpr<T>) {
            return (decl as? VarDecl<T>)?.newIndexed()?.ref ?: this
        }
        return map { it.unfold() }
    }

    private fun <T : Type> VarDecl<T>.newIndexed(): VarDecl<T> {
        val newName = this.name + "#" + indexing[this]
        indexing = indexing.inc(this)
        return IndexedVarDecl.of(newName, this)
    }

    private fun <T : Type> AssignStmt<T>.toSSA() = AssignStmt.of(varDecl.newIndexed(), expr.unfold())
    private fun AssumeStmt.toSSA() = AssumeStmt.of(cond.unfold())
    private fun <T : Type> HavocStmt<T>.toSSA() = HavocStmt.of(varDecl.newIndexed())
}
