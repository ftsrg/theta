/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import com.charleskorn.kaml.YamlPathSegment.Root.location
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.witnesses.*
import kotlinx.serialization.builtins.ListSerializer

class ApplyWitnessPass(parseContext: ParseContext) : ProcedurePass {
  private val witnessExample =
    """
- entry_type: "violation_sequence"
  metadata:
    format_version: "2.0"
    uuid: "5468f373-a912-4ad5-9308-58e43a204d54"
    creation_time: "2025-02-18T02:07:15Z"
    producer:
      name: "Theta"
      version: "no version found"
    task:
      input_files:
      - "Ex02.c"
      input_file_hashes:
        "Ex02.c": "afd40820c7a09c073d225c09c6690862ff04506300463cb312087d541b42d981"
      specification: "TERMINATION"
      data_model: "LP64"
      language: "C"
  content:
  - segment:
    - waypoint:
        type: "assumption"
        constraint:
          value: "i == 5"
          format: "c_expression"
        location:
          file_name: "Ex02.c"
          line: 7
          column: 32
        action: "follow"
  - segment:
    - waypoint:
        type: "recurrence_condition"
        constraint:
          value: "(i == 5)"
          format: "c_expression"
        location:
          file_name: "Ex02.c"
          line: 9
          column: 5
        action: "cycle"
  - segment:
    - waypoint:
        type: "branching"
        constraint:
          value: "false"
        location:
          file_name: "Ex02.c"
          line: 10
          column: 9
        action: "cycle"
  """
      .trimIndent()

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val witness =
      WitnessYamlConfig.decodeFromString(ListSerializer(YamlWitness.serializer()), witnessExample)
        .get(0)
    val segments = witness.content.map { c -> c.segment }.filterNotNull()
    val cycleWaypoints =
      segments
        .map { segment -> segment.find { waypoint -> waypoint.waypoint.action == Action.CYCLE } }
        .filterNotNull()
        .map { w -> w.waypoint }
    val followWaypoints =
      segments
        .map { segment -> segment.find { waypoint -> waypoint.waypoint.action == Action.FOLLOW } }
        .filterNotNull()
        .map { w -> w.waypoint }
    val recurrentSet =
      cycleWaypoints.find { waypoint -> waypoint.type == WaypointType.RECURRENCE_CONDITION }!!
    val allWaypoints = cycleWaypoints + followWaypoints

    // collect edges corresponding to recurrence location, cycle and follow waypoints
    val edgesOfWaypoints = mutableSetOf<XcfaEdge>()
    for (wayPoint in allWaypoints) {
      for (edge in builder.getEdges()) {
        val edgeMetadata = (edge.metadata as? CMetaData)
        if (edgeMetadata == null) {
          edgesOfWaypoints.add(edge) // if no metadata, keep it ?
        }
        if (edgeMetadata != null && edgeMetadata.lineNumberStart == wayPoint.location.line) {
          if (
            edgeMetadata.colNumberStart != null &&
              edgeMetadata.colNumberStart!! + 1 == wayPoint.location.column
          )
            edgesOfWaypoints.add(edge)
        }
        if (edgeMetadata != null && edgeMetadata.lineNumberStop == wayPoint.location.line) {
          if (
            edgeMetadata.colNumberStop != null &&
              edgeMetadata.colNumberStop!! + 1 == wayPoint.location.column
          )
            edgesOfWaypoints.add(edge)
        }
      }
    }

    // all edges, from which the waypoint edges are not reachable, should be removed
    val edgesToKeep = mutableSetOf<XcfaEdge>()
    val dist = floydWarshall(builder.getEdges())
    for (edgeToKeep in edgesOfWaypoints) {
      for (edge in builder.getEdges()) {
        if (dist[edge to edgeToKeep] != -1) {
          edgesToKeep.add(edge)
        }
      }
    }
    edgesToKeep.addAll(edgesOfWaypoints)

    val edgesToDelete = builder.getEdges().filter { edge -> edge !in edgesToKeep }.toMutableSet()

    for (edge in edgesToDelete) {
      builder.removeEdge(edge)
    }

    val locsToDelete = mutableSetOf<XcfaLocation>()

    // Removing unnecessary locations below

    // In a lasso, the initial location is the only location, which does not have an incoming edge
    // every other loc should have both incoming and outgoing edges

    // Also, we need to search and remove iteratively:
    // if we find a loc that should not be in the lasso, remove it first and then start searching
    // for the next
    // removing the location might uncover more locations that will have to be removed
    // e.g., if they have formed a chain and we want to remove the whole chain, not just the last
    // location
    var foundOne = true
    while (foundOne) {
      foundOne = false
      for (location in builder.getLocs()) {
        if (
          !location.initial &&
            (location.incomingEdges.isEmpty() || location.outgoingEdges.isEmpty())
        ) {
          foundOne = true
          locsToDelete.add(location)
          break
        }
      }
      for (loc in locsToDelete) {
        for (edge in loc.incomingEdges) {
          builder.removeEdge(edge)
        }
        for (edge in loc.outgoingEdges) {
          builder.removeEdge(edge)
        }
        builder.removeLoc(loc)
      }
    }

    return builder
  }

  private val inf = -1

  fun floydWarshall(edges: Set<XcfaEdge>): Map<Pair<XcfaEdge, XcfaEdge>, Int> {
    // Initialize distance map for edges
    val dist = mutableMapOf<Pair<XcfaEdge, XcfaEdge>, Int>()

    for (edge1 in edges) {
      for (edge2 in edges) {
        dist[edge1 to edge2] = if (edge1 == edge2) 0 else inf
      }
    }

    // Set initial distances based on connectivity
    for (edge1 in edges) {
      for (edge2 in edges) {
        if (edge1.target == edge2.source) { // Can transition from edge1 to edge2
          dist[edge1 to edge2] = 1 // Assuming unit weight
        }
      }
    }

    // Floyd-Warshall Algorithm for edge connectivity
    for (k in edges) {
      for (i in edges) {
        for (j in edges) {
          if (dist[i to k]!! != inf && dist[k to j]!! != inf) {
            if (dist[i to j]!! == inf) {
              dist[i to j] = dist[i to k]!! + dist[k to j]!!
            } else {
              dist[i to j] = minOf(dist[i to j]!!, dist[i to k]!! + dist[k to j]!!)
            }
          }
        }
      }
    }

    return dist
  }
}
