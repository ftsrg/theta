package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.*
import hu.bme.mit.theta.xcfa.model.*

class MutexToVarPass : ProcedurePass {

    private val mutexVars = mutableMapOf<String, VarDecl<BoolType>>()

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.replaceMutex()))
        }

        mutexVars.forEach { (_, v) -> builder.parent.addVar(XcfaGlobalVar(v, False())) }
        builder.parent.getInitProcedures().forEach { (proc, _) ->
            val initEdge = proc.initLoc.outgoingEdges.first()
            val initLabels = initEdge.getFlatLabels()
            mutexVars.forEach { (_, v) ->
                if (initLabels.none { it is StmtLabel && it.stmt is AssignStmt<*> && it.stmt.varDecl == v }) {
                    val assign = StmtLabel(AssignStmt.of(v, False()))
                    val label = SequenceLabel(initLabels + assign, metadata = initEdge.label.metadata)
                    proc.removeEdge(initEdge)
                    proc.addEdge(initEdge.withLabel(label))
                }
            }
        }
        return builder
    }

    private fun XcfaLabel.replaceMutex(): XcfaLabel {
        return when (this) {
            is SequenceLabel -> SequenceLabel(labels.map { it.replaceMutex() }, metadata)
            is FenceLabel -> {
                val actions = mutableListOf<XcfaLabel>()
                acquiredMutexes.filter { it != "" }.forEach {
                    actions.add(StmtLabel(AssumeStmt.of(Not(it.mutexFlag.ref))))
                    actions.add(StmtLabel(AssignStmt.of(it.mutexFlag, True())))
                }
                releasedMutexes.filter { it != "" }.forEach {
                    actions.add(StmtLabel(AssignStmt.of(it.mutexFlag, False())))
                }
                SequenceLabel(
                    (if (isAtomicBegin) listOf(FenceLabel(setOf("ATOMIC_BEGIN"))) else listOf())
                        + actions +
                        (if (isAtomicEnd) listOf(FenceLabel(setOf("ATOMIC_END"))) else listOf())
                )
                // Labels are atomic in XCFA semantics, so no need to wrap them in an atomic block
            }

            else -> this
        }
    }

    private val String.mutexFlag
        get() = mutexVars.getOrPut(this) { Decls.Var("_mutex_var_${ifEmpty { "atomic" }}", Bool()) }
}