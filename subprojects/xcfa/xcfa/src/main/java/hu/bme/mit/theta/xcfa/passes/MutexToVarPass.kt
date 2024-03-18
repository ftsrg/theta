package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.acquiredMutexes
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.releasedMutexes

class MutexToVarPass : ProcedurePass {

    private val mutexVars = mutableMapOf<String, VarDecl<BoolType>>()

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            builder.removeEdge(edge)
            builder.addEdge(edge.withLabel(edge.label.replaceMutex()))
        }

        mutexVars.forEach { (_, v) ->
            builder.parent.addVar(XcfaGlobalVar(v, False()))
        }

        builder.parent.getInitProcedures().forEach { (proc, _) ->
            val initEdge = proc.initLoc.outgoingEdges.first()
            val initLabels = initEdge.getFlatLabels()
            mutexVars.forEach { (_, v) ->
                if (initLabels.none { it is StmtLabel && it.stmt is AssignStmt<*> && it.stmt.varDecl == v }) {
                    val assign = StmtLabel(AssignStmt.of(v, False()), metadata = EmptyMetaData)
                    val label = SequenceLabel(initLabels + assign, metadata = initEdge.label.metadata)
                    proc.addEdge(initEdge.withLabel(label))
                    proc.removeEdge(initEdge)
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
                acquiredMutexes.forEach {
                    val cond = AssumeStmt.of(Not(it.mutexFlag.ref))
                    actions.add(StmtLabel(cond, metadata = EmptyMetaData))
                    val assign = AssignStmt.of(it.mutexFlag, True())
                    actions.add(StmtLabel(assign, metadata = EmptyMetaData))
                }
                releasedMutexes.forEach {
                    val assign = AssignStmt.of(it.mutexFlag, False())
                    actions.add(StmtLabel(assign, metadata = EmptyMetaData))
                }
                // Labels are atomic in XCFA semantics, so no need to wrap them in an atomic block
                SequenceLabel(actions)
            }

            else -> this
        }
    }

    private val String.mutexFlag
        get() = mutexVars.getOrPut(this) { Decls.Var("_mutex_var_${ifEmpty { "atomic" }}", Bool()) }
}