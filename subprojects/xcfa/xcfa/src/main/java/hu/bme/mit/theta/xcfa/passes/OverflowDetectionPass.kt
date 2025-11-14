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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.IfStmt
import hu.bme.mit.theta.core.stmt.LoopStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.OrtStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.MulExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getLimitVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.AtomicBeginLabel
import hu.bme.mit.theta.xcfa.model.AtomicEndLabel
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.JoinLabel
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.MutexLockLabel
import hu.bme.mit.theta.xcfa.model.MutexTryLockLabel
import hu.bme.mit.theta.xcfa.model.MutexUnlockLabel
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.RWLockReadLockLabel
import hu.bme.mit.theta.xcfa.model.RWLockUnlockLabel
import hu.bme.mit.theta.xcfa.model.RWLockWriteLockLabel
import hu.bme.mit.theta.xcfa.model.ReturnLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class OverflowDetectionPass(val property: XcfaProperty, val parseContext: ParseContext) :
  ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {

    if (property.inputProperty != ErrorDetection.OVERFLOW) {
      return builder
    }

    check(parseContext.arithmetic != ArchitectureConfig.ArithmeticType.bitvector) {
      "Overflow checking does not yet support bitwise arithmetic"
    }

    property.transformSpecification(ErrorDetection.ERROR_LOCATION)

    // remove all edges to the error location

    val errorLoc =
      builder.errorLoc
        .map {
          it.incomingEdges.forEach(builder::removeEdge)
          it
        }
        .or {
          builder.createErrorLoc()
          builder.errorLoc
        }
        .get()

    val limitVisitor = getLimitVisitor(parseContext)

    // tracks which edges need work; where we insert an edge to error _before_ the indexed label
    val toInsert = mutableMapOf<XcfaEdge, MutableList<Pair<Int, Expr<BoolType>>>>()

    for (edge in builder.getEdges()) {
      edge.getFlatLabels().forEachIndexed { i, label ->
        val conditions =
          label
            .getExpressions {
              (it is AddExpr || it is SubExpr || it is MulExpr || it is DivExpr || it is NegExpr) &&
                parseContext.metadata
                  .getMetadataValue(it, "cType")
                  .map { cType -> (cType as? CInteger)?.isSsigned ?: false }
                  .orElse(false)
            }
            .map {
              val cType =
                parseContext.metadata
                  .getMetadataValue(it, "cType")
                  .or { parseContext.metadata.getMetadataValue((it as IteExpr).then, "cType") }
                  .get() as CComplexType
              Not(cType.accept(limitVisitor, it).cond)
            }

        if (conditions.isNotEmpty()) {
          val overflow = Or(conditions)
          toInsert.computeIfAbsent(edge) { mutableListOf() }.add(i to overflow)
        }
      }
    }

    toInsert.forEach { (edge, breakpoints) ->
      val newEdges = mutableListOf<XcfaEdge>()
      val oldLabels = edge.getFlatLabels()
      val edgeBuilder = mutableListOf<XcfaLabel>()
      var i = 0
      var j = 0
      var source = edge.source

      fun flushToEdges(target: XcfaLocation) {
        if (edgeBuilder.isEmpty()) return
        val metadata = edgeBuilder.map(XcfaLabel::metadata).reduce(MetaData::combine)
        newEdges.add(
          XcfaEdge(
            source,
            target,
            SequenceLabel(edgeBuilder.toList(), metadata = metadata),
            metadata = metadata,
          )
        )
        edgeBuilder.clear()
        source = target
      }

      while (i < oldLabels.size) {
        if (j >= breakpoints.size || i < breakpoints[j].first) {
          // continue building edge
          edgeBuilder.add(oldLabels[i])
          i++
        } else {
          // found a point to break, definitely not last, so let's make a new anonymous loc
          val target =
            XcfaLocation(
              "__overflow__" + XcfaLocation.uniqueCounter() + "__tmp",
              metadata = edge.source.metadata,
            )
          flushToEdges(target)
          builder.addEdge(
            XcfaEdge(
              source,
              errorLoc,
              StmtLabel(AssumeStmt.of(breakpoints[j].second), metadata = oldLabels[i].metadata),
              metadata = oldLabels[i].metadata,
            )
          )
          edgeBuilder.add(
            StmtLabel(AssumeStmt.of(Not(breakpoints[j].second)))
          ) // so the assumption-branchings look deterministic
          j++
        }
      }
      flushToEdges(edge.target)
      builder.removeEdge(edge)
      newEdges.forEach(builder::addEdge)
    }

    return SimplifyExprsPass(parseContext, property).run(builder)
  }
}

private fun XcfaLabel.getExpressions(f: (Expr<*>) -> Boolean): Set<Expr<*>> =
  when (this) {
    is AtomicBeginLabel,
    is AtomicEndLabel,
    is MutexLockLabel,
    is MutexTryLockLabel,
    is MutexUnlockLabel,
    is RWLockReadLockLabel,
    is RWLockUnlockLabel,
    is RWLockWriteLockLabel,
    NopLabel -> setOf()
    is InvokeLabel -> params.flatMap { it.getExpressions(f) }.toSet()
    is NondetLabel -> labels.flatMap { it.getExpressions(f) }.toSet()
    is ReturnLabel -> enclosedLabel.getExpressions(f)
    is SequenceLabel -> labels.flatMap { it.getExpressions(f) }.toSet()
    is StartLabel -> (params.flatMap { it.getExpressions(f) } + handle.getExpressions(f)).toSet()
    is JoinLabel -> handle.getExpressions(f)
    is StmtLabel -> stmt.getExpressions(f)
  }

private fun Stmt.getExpressions(f: (Expr<*>) -> Boolean): Set<Expr<*>> =
  when (this) {
    is AssignStmt<*> -> expr.getExpressions(f)
    is AssumeStmt -> cond.getExpressions(f)
    is HavocStmt<*> -> setOf()
    is IfStmt -> cond.getExpressions(f) + elze.getExpressions(f) + then.getExpressions(f)
    is LoopStmt -> stmt.getExpressions(f)
    is MemoryAssignStmt<*, *, *> -> expr.getExpressions(f)
    is NonDetStmt -> stmts.flatMap { it.getExpressions(f) }.toSet()
    is OrtStmt -> stmts.flatMap { it.getExpressions(f) }.toSet()
    is SequenceStmt -> stmts.flatMap { it.getExpressions(f) }.toSet()
    is SkipStmt -> setOf()
    else -> throw IllegalArgumentException("Unknown stmt type: $this")
  }

private fun Expr<*>.getExpressions(
  f: (Expr<*>) -> Boolean,
  shortCircuitCondition: Expr<BoolType> = TrueExpr.getInstance(),
): Set<Expr<*>> {
  if (this is DivExpr<*>) {
    throw UnsupportedOperationException("We cannot soundly detect overflows with divisions.")
  }
  var shortCircuitCondition: Expr<BoolType> = shortCircuitCondition
  val ret = mutableSetOf<Expr<*>>()
  for (expr in ops) {
    ret.addAll(expr.getExpressions(f, shortCircuitCondition))
    shortCircuitCondition =
      when (this) {
        is OrExpr -> And(shortCircuitCondition, Not(expr as Expr<BoolType>))
        is AndExpr -> And(shortCircuitCondition, expr as Expr<BoolType>)
        else -> shortCircuitCondition
      }
  }
  if (f(this)) {
    if (shortCircuitCondition == TrueExpr.getInstance()) {
      ret.add(this)
    } else {
      val ite = IteExpr.of(shortCircuitCondition, this as Expr<IntType>, Int(0))
      ret.add(ite)
    }
  }
  return ret
}
