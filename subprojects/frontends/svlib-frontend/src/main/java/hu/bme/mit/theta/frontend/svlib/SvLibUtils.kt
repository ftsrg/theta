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

package hu.bme.mit.theta.frontend.svlib

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.Interval

internal fun newLoc(tags: List<String> = listOf())
  = XcfaLocation("l" + XcfaLocation.uniqueCounter(), metadata = SvLibTagMetadata(tags))

internal fun XcfaProcedureBuilder.insertCheck(location: XcfaLocation, condition: Expr<BoolType>): XcfaLocation {
  val originalOutgoingEdges = location.outgoingEdges.toMutableList()
  val nextLoc = newLoc()

  addEdge(XcfaEdge(location, errorLoc.get(), StmtLabel(Assume(Not(condition))), location.metadata))
  addEdge(XcfaEdge(location, nextLoc, StmtLabel(Assume(condition)), location.metadata))

  originalOutgoingEdges.forEach {
    removeEdge(it)
    addEdge(it.withSource(nextLoc))
  }

  return nextLoc
}

internal fun sortOf(sort: SortContext): Type =
  when (sort) {
    is SimpleSortContext -> when (sort.identifier().text) {
      "Int" -> IntExprs.Int()
      "Bool" -> BoolExprs.Bool()
      else -> throw sort.unsupported("sort '${sort.text}'")
    }
    is ParametricSortContext -> when (sort.identifier().text) {
      "Array" -> {
        val indexType: Type = sortOf(sort.sort(0))
        val elementType: Type = sortOf(sort.sort(1))
        ArrayExprs.Array(indexType, elementType)
      }

      else -> throw sort.unsupported("sort '${sort.text}'")
    }
    else -> throw sort.unsupported("sort '${sort.text}'")
  }

internal fun unsupported(message: String) =
  UnsupportedOperationException("Unsupported SV-LIB element: $message")

internal fun ParserRuleContext.unsupported(message: String) =
  UnsupportedOperationException("Unsupported SV-LIB element (${start.line}:${start.charPositionInLine}): $message")

open class SvLibVisitor<T>(protected val charStream: CharStream, protected val logger: Logger)
  : SvLibBaseVisitor<T>() {
  val ParserRuleContext.original: String
    get() = charStream.getText(Interval(this.start.startIndex, this.stop.stopIndex))

  fun warn(message: String) {
    logger.writeln(Logger.Level.INFO, "WARNING: $message")
  }
}

fun <K, V> MutableMap<K, V>.putAll(from: Map<out K, V>, conflictResolution: (V, V) -> V) {
  for ((key, value) in from) {
    this[key] = this[key]?.let { conflictResolution(it, value) } ?: value
  }
}

fun <T> ArrayDeque<T>.push(elem: T) = addLast(elem)

fun <T> ArrayDeque<T>.peak() = last()

fun <T> ArrayDeque<T>.pop() = removeLast()
