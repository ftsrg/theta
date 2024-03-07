package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*

class AssumeFalseRemovalPass : ProcedurePass {

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        builder.getEdges().toSet().forEach { edge ->
            if (edge.getFlatLabels()
                    .any { it is StmtLabel && it.stmt is AssumeStmt && (it.stmt as AssumeStmt).cond is FalseExpr }) {
                builder.removeEdge(edge)
            }
        }

        val getUnreachable: () -> List<XcfaLocation> = {
            builder.getLocs().filter { it.incomingEdges.isEmpty() && !it.initial }
        }
        var unreachable = getUnreachable()
        while (unreachable.isNotEmpty()) {
            unreachable.forEach { loc ->
                loc.outgoingEdges.forEach { builder.removeEdge(it) }
                builder.removeLoc(loc)
            }
            unreachable = getUnreachable()
        }
        return builder
    }
}
