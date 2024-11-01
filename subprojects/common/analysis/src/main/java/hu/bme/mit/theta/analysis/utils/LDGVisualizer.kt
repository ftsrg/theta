/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.utils

import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGEdge
import hu.bme.mit.theta.analysis.algorithm.asg.ASGNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.common.visualization.Alignment.LEFT
import hu.bme.mit.theta.common.visualization.Shape.RECTANGLE
import java.awt.Color

class AsgVisualizer<S : ExprState, A : ExprAction>(
  private val stateToString: (S) -> String,
  private val actionToString: (A) -> String,
) : ProofVisualizer<ASG<S, A>> {

  private var traceNodes: MutableSet<ASGNode<out S, out A>> = mutableSetOf()
  private var traceEdges: MutableSet<ASGEdge<out S, out A>> = mutableSetOf()

  override fun visualize(ASG: ASG<S, A>): Graph {
    traceNodes = mutableSetOf()
    traceEdges = mutableSetOf()
    return createVisualization(ASG)
  }

  fun visualize(ASG: ASG<out S, out A>, trace: ASGTrace<out S, out A>): Graph {
    traceEdges = mutableSetOf()
    traceEdges.addAll(trace.edges)
    traceNodes = mutableSetOf()
    trace.edges.map { it.source!! }.forEach(traceNodes::add)
    return createVisualization(ASG)
  }

  private fun createVisualization(ASG: ASG<out S, out A>): Graph {
    val graph = Graph(LDG_ID, LDG_LABEL)

    val traversed: MutableSet<ASGNode<out S, out A>> = mutableSetOf()

    for (initNode in ASG.initNodes) {
      traverse(graph, initNode, traversed)
      val nAttributes =
        NodeAttributes.builder()
          .label("")
          .fillColor(FILL_COLOR)
          .lineColor(FILL_COLOR)
          .lineStyle(SUCC_EDGE_STYLE)
          .peripheries(1)
          .build()
      graph.addNode(PHANTOM_INIT_ID + initNode.id, nAttributes)
      val eAttributes =
        EdgeAttributes.builder()
          .label("")
          .color(if (traceNodes.contains(initNode)) TARGET_COLOR else LINE_COLOR)
          .lineStyle(SUCC_EDGE_STYLE)
          .build()
      graph.addEdge(PHANTOM_INIT_ID + initNode.id, NODE_ID_PREFIX + initNode.id, eAttributes)
    }

    return graph
  }

  private fun traverse(
    graph: Graph,
    node: ASGNode<out S, out A>,
    traversed: MutableSet<ASGNode<out S, out A>>,
  ) {
    if (traversed.contains(node)) {
      return
    } else {
      traversed.add(node)
    }
    val nodeId = NODE_ID_PREFIX + node.id
    val peripheries = if (node.accepting) 2 else 1

    val nAttributes =
      NodeAttributes.builder()
        .label(stateToString(node.state))
        .alignment(LEFT)
        .shape(RECTANGLE)
        .font(FONT)
        .fillColor(FILL_COLOR)
        .lineColor(if (traceNodes.contains(node)) TARGET_COLOR else LINE_COLOR)
        .lineStyle(SUCC_EDGE_STYLE)
        .peripheries(peripheries)
        .build()

    graph.addNode(nodeId, nAttributes)

    for (edge in node.outEdges) {
      traverse(graph, edge.target, traversed)
      val sourceId = NODE_ID_PREFIX + edge.source?.id
      val targetId = NODE_ID_PREFIX + edge.target.id
      val eAttributes =
        EdgeAttributes.builder()
          .label(actionToString(edge.action!!))
          .alignment(LEFT)
          .font(FONT)
          .color(if (traceEdges.contains(edge)) TARGET_COLOR else LINE_COLOR)
          .lineStyle(if (edge.accepting) LineStyle.DASHED else SUCC_EDGE_STYLE)
          .build()
      graph.addEdge(sourceId, targetId, eAttributes)
    }
  }

  companion object {

    private val SUCC_EDGE_STYLE = LineStyle.NORMAL
    private const val LDG_LABEL = ""
    private const val LDG_ID = "ldg"
    private const val FONT = "courier"
    private const val NODE_ID_PREFIX = "node_"
    private val FILL_COLOR: Color = Color.WHITE
    private val LINE_COLOR: Color = Color.BLACK
    private val TARGET_COLOR: Color = Color.RED
    private const val PHANTOM_INIT_ID = "phantom_init"
  }
}
