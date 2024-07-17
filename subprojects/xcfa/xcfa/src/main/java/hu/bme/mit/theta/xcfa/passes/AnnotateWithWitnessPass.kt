package hu.bme.mit.theta.xcfa.passes

import com.google.common.base.Preconditions
import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.SequenceStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.witness.yaml.serialization.WaypointType
import hu.bme.mit.theta.metadata.CMetaData
import hu.bme.mit.theta.witness.yaml.model.*
import hu.bme.mit.theta.witness.yaml.serialization.ActionEnum
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*

/**
 * Annotates XCFA with information from a software witness
 * Works with the witness 2.0 non-termination witnesses
 */
class AnnotateWithWitnessPass : ProcedurePass {
    companion object {
        lateinit var witness: Witness2
        var enabled = false
    }

    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        if (!enabled) return builder
        // TODO metadata check, here or earlier..?
        for (entry in witness.entries) {
            for (item in entry.content.items) {
                when (item) {
                    is Cycle -> {
                        annotateWithCycle(item, builder)
                    }

                    is Segment -> {
                        annotateWithSegment(item, builder)
                    }
                }
            }
        }
        return builder
    }

    private fun annotateWithSegment(segment: Segment, builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        var b = builder
        for (waypoint in segment.waypoint) {
            b = annotateWithWaypoint(waypoint, b)
        }
        return b
    }

    private fun annotateWithWaypoint(waypoint : Waypoint, builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        return when (waypoint.type) {
            WaypointType.ASSUMPTION -> TODO()
            WaypointType.TARGET -> TODO()
            WaypointType.FUNCTION_ENTER -> TODO()
            WaypointType.FUNCTION_RETURN -> TODO()
            WaypointType.BRANCHING -> annotateBranching(waypoint, builder)
        }
    }

    /**
     * Branching waypoint shows which way we took in that branch
     */
    private fun annotateBranching(
        waypoint: Waypoint,
        builder: XcfaProcedureBuilder
    ) : XcfaProcedureBuilder {
        val newEdges = mutableMapOf<XcfaEdge, XcfaEdge>()
        for(loc in builder.getLocs()) {
            if(loc.outgoingEdges.size==2 && loc.outgoingEdges.all { it.getCMetaData()?.lineNumberStart == waypoint.location.line && it.getCMetaData()?.colNumberStart == waypoint.location.column }) {
                for(edge in loc.outgoingEdges) {
                    checkState(edge.label is SequenceLabel)
                    if(edge.label is SequenceLabel) {
                        // there must be a constraint, we know it's a branching
                        if((waypoint.constraint!!.value=="true" && waypoint.action==ActionEnum.FOLLOW) || (waypoint.constraint!!.value=="false" && waypoint.action==ActionEnum.AVOID)) {
                            if(edge.getFlatLabels().any { it is StmtLabel && it.choiceType == ChoiceType.MAIN_PATH }) {
                                newEdges[edge] = XcfaEdge(edge.source, edge.target, edge.metadata, SequenceLabel(
                                    (listOf(
                                        StmtLabel(Assume(BoolExprs.True()), edge.metadata)) + edge.label.labels
                                            ),
                                    edge.metadata
                                ))
                            } else if(edge.getFlatLabels().any { it is StmtLabel && it.choiceType == ChoiceType.ALTERNATIVE_PATH }) {
                                newEdges[edge] = XcfaEdge(edge.source, edge.target, edge.metadata, SequenceLabel(
                                    (listOf(
                                        StmtLabel(Assume(BoolExprs.False()), edge.metadata)) + edge.label.labels
                                            ),
                                    edge.metadata
                                ))
                            }

                        } else if((waypoint.constraint!!.value=="false" && waypoint.action==ActionEnum.FOLLOW) || (waypoint.constraint!!.value=="true" && waypoint.action==ActionEnum.AVOID)) {
                            if(edge.getFlatLabels().any { it is StmtLabel && it.choiceType == ChoiceType.ALTERNATIVE_PATH }) {
                                newEdges[edge] = XcfaEdge(edge.source, edge.target, edge.metadata, SequenceLabel(
                                    (listOf(
                                        StmtLabel(Assume(BoolExprs.True()), edge.metadata)) + edge.label.labels
                                            ),
                                    edge.metadata
                                ))
                            } else if(edge.getFlatLabels().any { it is StmtLabel && it.choiceType == ChoiceType.MAIN_PATH }) {
                                newEdges[edge] = XcfaEdge(edge.source, edge.target, edge.metadata, SequenceLabel(
                                    (listOf(
                                        StmtLabel(Assume(BoolExprs.False()), edge.metadata)) + edge.label.labels
                                            ),
                                    edge.metadata
                                ))
                            }
                        } else {
                            throw RuntimeException("Branching waypoint with unknown constrain-action combination: ${waypoint.constraint!!.value}, ${waypoint.action}")
                        }
                    }
                }
            }

        }
        for(edgePair in newEdges.entries) {
            builder.addEdge(edgePair.key)
            builder.removeEdge(edgePair.value)
        }
        return builder
    }

    private fun annotateWithCycle(cycle: Cycle, builder : XcfaProcedureBuilder) : XcfaProcedureBuilder {
        var b = builder
        for(item in cycle.items) {
            b = when (item) {
                is Segment -> annotateWithSegment(item, b)
                is Honda -> b // xcfa is not annotated with the honda, it is used elsewhere
                else -> {
                    throw RuntimeException("Unexpected item type ${item.javaClass.canonicalName}")
                }
            }
        }
        return b
    }
}

fun XcfaEdge.getCMetaData(): CMetaData? {
    return if (this.metadata is CMetaData) {
        this.metadata as CMetaData
    } else {
        null
    }
}

fun XcfaLabel.getCMetaData(): CMetaData? {
    return if (this.metadata is CMetaData) {
        this.metadata as CMetaData
    } else {
        null
    }
}

fun XcfaLocation.getCMetaData(): CMetaData? {
    return if (this.metadata is CMetaData) {
        this.metadata as CMetaData
    } else {
        null
    }
}