/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression

import hu.bme.mit.delta.collections.IntObjMapView
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddGraph
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddVariableHandle
import hu.bme.mit.delta.java.mdd.UnaryOperationCache
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityTemplate

object MddExplicitRepresentationExtractor {

  /**
   * Builds a variable order mirroring [top]'s chain on a fresh graph. Extracting through it keeps
   * the explicit nodes out of the source order's unique tables, where hash collisions with the
   * procedural expression nodes force solver-driven equality enumeration.
   */
  fun mirrorTopOf(top: MddVariableHandle): MddVariableHandle {
    val mirrorOrder =
      JavaMddFactory.getDefault().createMddVariableOrder(ExprLatticeDefinition.forExpr())
    generateSequence(top) { it.lower.orElse(null) }
      .mapNotNull { it.variable.orElse(null) }
      .toList()
      .asReversed()
      .forEach { mirrorOrder.createOnTop(MddVariableDescriptor.copy(it)) }
    return mirrorOrder.defaultSetSignature.topVariableHandle
  }

  fun transform(node: MddHandle, variable: MddVariableHandle): MddHandle =
    transform(node, variable, dataBoundary = null)

  /**
   * Extracts [node] into the [variable] order. With a non-null [dataBoundary] the walk is truncated at
   * that level — every variable at and below it is accepted (the lattice top) — and only the edges
   * exploration actually consumed (visited via get or cursor) are extracted: the explicit caches also
   * hold seeded entries the iteration never touched, which must not widen the bound.
   */
  fun transform(node: MddHandle, variable: MddVariableHandle, dataBoundary: Any?): MddHandle =
    transform(node, variable, UnaryOperationCache(), dataBoundary)

  fun transform(
    node: MddHandle,
    variable: MddVariableHandle,
    cache: UnaryOperationCache<MddHandle, MddHandle>,
    dataBoundary: Any?,
  ): MddHandle {
    cache.getOrNull(node)?.let {
      return it
    }

    val result: MddHandle =
      when {
        node.isTerminalZero -> variable.mddGraph.terminalZeroHandle
        node.isTerminal -> {
          val mddGraph: MddGraph<Any> = variable.mddGraph as MddGraph<Any>
          mddGraph.terminalVariableHandle.getHandleFor(mddGraph.getNodeFor(node.data))
        }
        dataBoundary != null && atBoundary(node.variableHandle, dataBoundary) ->
          variable.mddGraph.handleForTop
        node.isSkippedLevel -> {
          val s =
            transform(
              lowerOf(node.variableHandle).getHandleFor(node.node),
              lowerOf(variable),
              cache,
              dataBoundary,
            )
          if (s.isTerminalZero) variable.mddGraph.terminalZeroHandle
          else variable.checkInNode(MddStructuralTemplate.of(IntObjMapView.empty(s.node)))
        }
        node.node.representation is IdentityRepresentation -> {
          val s =
            transform(
              node.variableHandle.lower
                .get()
                .lower
                .get()
                .getHandleFor((node.node.representation as IdentityRepresentation).continuation),
              variable.lower.get().lower.orElse(null),
              cache,
              dataBoundary,
            )
          if (!s.isTerminalZero) variable.checkInNode(IdentityTemplate(s.node))
          else variable.mddGraph.terminalZeroHandle
        }
        node.node.representation is MddExpressionRepresentation -> {
          val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()
          val explored = (node.node.representation as MddExpressionRepresentation).explored()
          val knownEdges = explored.knownEdges()
          if (knownEdges.defaultValue() != null) {
            val s =
              transform(
                node.variableHandle.lower.get().getHandleFor(knownEdges.defaultValue()),
                variable.lower.orElse(null),
                cache,
                dataBoundary,
              )
            if (!s.isTerminalZero) templateBuilder.setDefault(s.node)
          } else if (dataBoundary != null) {
            val keys = explored.visitedKeys().cursor()
            while (keys.moveNext()) {
              val child = knownEdges.get(keys.elem()) ?: continue
              val s =
                transform(
                  node.variableHandle.lower.get().getHandleFor(child),
                  variable.lower.orElse(null),
                  cache,
                  dataBoundary,
                )
              if (!s.isTerminalZero) templateBuilder.set(keys.elem(), s.node)
            }
          } else {
            val cursor = knownEdges.cursor()
            while (cursor.moveNext()) {
              val s =
                transform(
                  node.variableHandle.lower.get().getHandleFor(cursor.value()),
                  variable.lower.orElse(null),
                  cache,
                  dataBoundary,
                )
              if (!s.isTerminalZero) templateBuilder.set(cursor.key(), s.node)
            }
          }
          variable.checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset()))
        }
        else -> error("Unexpected representation in extraction: ${node.node.representation}")
      }

    cache.addToCache(node, result)
    return result
  }

  private fun atBoundary(varHandle: MddVariableHandle, dataBoundary: Any): Boolean =
    varHandle.variable.map { it.traceInfo }.orElse(null) == dataBoundary

  private fun lowerOf(varHandle: MddVariableHandle): MddVariableHandle =
    if (varHandle.lower.isPresent) varHandle.lower.get()
    else varHandle.mddGraph.terminalVariableHandle
}
