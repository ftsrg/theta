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

    val builder = XcfaBuilder(
        name = "${name}_SSA",
        vars = vars.toMutableSet()
    )
    procedureBuilders.forEach { builder.addProcedure(it.copy()) }
    initProcedureBuilders.forEach { (proc, params) ->
        val initProc = builder.getProcedures().find { it.name == proc.name } ?: proc.copy()
        builder.addEntryPoint(initProc, params)
    }
    return builder.build()
}

class SSAPass : ProcedurePass {

    private var indexing: VarIndexing = VarIndexingFactory.indexing(0)

    val vars = mutableSetOf<VarDecl<*>>()

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

            is StartLabel -> {
                val newParams = params.map { it.unfold(indexing) }
                params.flatMap { ExprUtils.getVars(it) }.forEach { indexing = indexing.inc(it) }
                val newPidVar = pidVar.getIndexedVarDecl(indexing[pidVar])
                indexing = indexing.inc(pidVar)
                StartLabel(name, newParams, newPidVar, metadata, tempLookup)
            }

            is JoinLabel -> {
                val newPidVar = pidVar.getIndexedVarDecl(indexing[pidVar])
                indexing = indexing.inc(pidVar)
                JoinLabel(newPidVar, metadata)
            }

            is SequenceLabel -> SequenceLabel(labels.map { it.unfold() }, metadata)
            is NopLabel, is FenceLabel -> this
            else -> error("Unsupported label at SSA conversion: $this")
        }
    }

    private fun <T : Type> VarDecl<T>.getIndexedVarDecl(index: Int): VarDecl<T> {
        val newName = this.name + "#" + index
        vars.find { it.name == newName }?.let { return it as VarDecl<T> }
        val newVar = IndexedVarDecl.of(newName, this)
        vars.add(newVar)
        return newVar
    }

    private fun <T : Type> AssignStmt<T>.toSSA(): AssignStmt<T> {
        val rhsSSA = expr.unfold(indexing)
        ExprUtils.getVars(expr).forEach { indexing = indexing.inc(it) }
        val lhsSSA = varDecl.getIndexedVarDecl(indexing[varDecl])
        indexing = indexing.inc(varDecl)
        return AssignStmt.of(lhsSSA, rhsSSA)
    }

    private fun AssumeStmt.toSSA(): AssumeStmt {
        val condSSA = cond.unfold(indexing)
        ExprUtils.getVars(cond).forEach { indexing = indexing.inc(it) }
        return AssumeStmt.of(condSSA)
    }

    private fun <T : Type> HavocStmt<T>.toSSA(): HavocStmt<T> {
        val lhsSSA = varDecl.getIndexedVarDecl(indexing[varDecl])
        indexing = indexing.inc(varDecl)
        return HavocStmt.of(lhsSSA)
    }

    private fun <T : Type> Expr<T>.unfold(indexing: VarIndexing): Expr<T> {
        if (this is RefExpr<T>) {
            val decl = this.decl
            if (decl is VarDecl<T>) return decl.getIndexedVarDecl(indexing[decl]).ref
        }
        return map { it.unfold(indexing) }
    }

}
