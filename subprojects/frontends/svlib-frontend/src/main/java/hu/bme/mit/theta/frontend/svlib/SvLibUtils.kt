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
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.strongLiveVars
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.Interval

internal fun newLoc(prefix: String = "l", tags: Set<String> = setOf(), procedure: String? = null) =
  XcfaLocation(prefix + XcfaLocation.uniqueCounter(), metadata = SvLibTagMetadata(tags, procedure))

// passes keep metadata, so information relevant for witnesses is stored there
internal fun witnessStep(metadata: SvLibWitnessMetadata) =
  StmtLabel(Stmts.Skip(), metadata = metadata)

fun XcfaLabel.isWitnessStep() =
  this is StmtLabel && stmt is SkipStmt && (metadata as? SvLibWitnessMetadata) != null

private var tmpVarCnt = 0
const val tmpVarPrefix = "__theta"
const val GLOBAL_SCOPE = "__theta_global"

internal fun VarDecl<*>.createTemp() = Decls.Var("${tmpVarPrefix}_${name}_${tmpVarCnt++}", type)

internal fun XcfaProcedureBuilder.insertCheck(
  location: XcfaLocation,
  condition: Expr<BoolType>,
  metadata: SvLibWitnessMetadata,
): XcfaLocation {
  val originalOutgoingEdges = location.outgoingEdges.toMutableList()
  val nextLoc = newLoc()

  addEdge(
    XcfaEdge(
      location,
      errorLoc.get(),
      StmtLabel(Assume(Not(condition)), metadata = metadata),
      metadata,
    )
  )
  addEdge(XcfaEdge(location, nextLoc, StmtLabel(Assume(condition), metadata = metadata), metadata))

  originalOutgoingEdges.forEach {
    removeEdge(it)
    addEdge(it.withSource(nextLoc))
  }

  return nextLoc
}

internal fun XcfaProcedureBuilder.havocUninitializedVars() {
  val initEdge = initLoc.outgoingEdges.singleOrNull() ?: return
  val liveVars = strongLiveVars(this)[initLoc].orEmpty()

  val uninits =
    getVars()
      .filter { getParams().all { (param, dir) -> param != it || dir == ParamDirection.OUT } }
      .filter { it in liveVars }
      .map { StmtLabel(Stmts.Havoc(it), metadata = initEdge.metadata) }

  removeEdge(initEdge)
  addEdge(initEdge.withLabel(SequenceLabel(initEdge.getAllLabels() + uninits, initEdge.metadata)))
}

internal fun ParserRuleContext.unsupported(message: String) =
  UnsupportedOperationException(
    "Unsupported SV-LIB element (${start.line}:${start.charPositionInLine}): $message"
  )

internal fun ParserRuleContext.illegal(message: String) =
  IllegalStateException("Invalid statement (${start.line}:${start.charPositionInLine}): $message")

open class SvLibVisitor<T>(protected val charStream: CharStream, protected val logger: Logger) :
  SvLibBaseVisitor<T>() {
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
