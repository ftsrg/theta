package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.acquiredMutexes
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.releasedMutexes

class MutexToVarPass : ProcedurePass {

    private val mutexVars = mutableMapOf<String, VarDecl<BoolType>>()

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.replaceMutex()))
        }
        return builder
    }

    private fun XcfaLabel.replaceMutex(): XcfaLabel {
        return when (this) {
            is SequenceLabel -> SequenceLabel(labels.map { it.replaceMutex() }, metadata)
            is FenceLabel -> {
                val actions = mutableListOf<XcfaLabel>(FenceLabel(setOf("MUTEX_FLAG_SET"), EmptyMetaData))
                acquiredMutexes.forEach {
                    val cond = AssumeStmt.of(mutexVars.getOrPut(it) { Decls.Var(it, Bool()) }.ref)
                    actions.add(StmtLabel(cond, metadata = EmptyMetaData))
                    val assign = AssignStmt.of(mutexVars[it]!!, True())
                    actions.add(StmtLabel(assign, metadata = EmptyMetaData))
                }
                releasedMutexes.forEach {
                    val assign = AssignStmt.of(mutexVars.getOrPut(it) { Decls.Var(it, Bool()) }, False())
                    actions.add(StmtLabel(assign, metadata = EmptyMetaData))
                }
                actions.add(FenceLabel(setOf("MUTEX_FLAG_UNSET"), EmptyMetaData))
                SequenceLabel(actions)
            }

            else -> this
        }
    }
}