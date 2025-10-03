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
package hu.bme.mit.theta.cfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.ProofConservingModelToMonolithicAdapter
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign
import hu.bme.mit.theta.core.type.fptype.FpExprs.NaN
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import java.math.BigInteger

class CfaToMonolithicAdapter(override val model: CFA) :
  ProofConservingModelToMonolithicAdapter<CFA, CfaState<ExplState>, CfaAction> {

  lateinit var locationIndexes: Map<CFA.Loc, Int>
  lateinit var indexedEdges: Map<Pair<Int, Int>, CFA.Edge>
  lateinit var locVar: VarDecl<IntType>

  override val monolithicExpr: MonolithicExpr get() {
    Preconditions.checkArgument(model.errorLoc.isPresent)
    locationIndexes = model.locs.mapIndexed { index, loc -> loc to index }.toMap()
    locVar = Decls.Var("__loc__", Int())
    indexedEdges =
      model.edges.associateBy { edge ->
        Pair(locationIndexes[edge.source]!!, locationIndexes[edge.target]!!)
      }
    val tranList =
      indexedEdges
        .map { entry ->
          val (sourceIndex, targetIndex) = entry.key
          SequenceStmt.of(
            listOf(
              AssumeStmt.of(Eq(locVar.ref, Int(sourceIndex))),
              entry.value.stmt,
              AssignStmt.of(locVar, Int(targetIndex)),
            )
          )
        }
        .toList()

    val defaultValues =
      model.vars
        .map {
          when (it.type) {
            is IntType -> Eq(it.ref, Int(0))
            is BoolType -> Eq(it.ref, Bool(false))
            is BvType ->
              Eq(
                it.ref,
                BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, (it.type as BvType).size),
              )
            is FpType -> FpAssign(it.ref as Expr<FpType>, NaN(it.type as FpType))
            else -> throw IllegalArgumentException("Unsupported type")
          }
        }
        .toList()
        .let { And(it) }

    val trans = NonDetStmt.of(tranList)
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))
    val transExpr = And(transUnfold.exprs)
    val initExpr = And(Eq(locVar.ref, Int(locationIndexes[model.initLoc]!!)), defaultValues)
    val propExpr = Neq(locVar.ref, Int(locationIndexes[model.errorLoc.orElseThrow()]!!))

    return MonolithicExpr(
      initExpr,
      transExpr,
      propExpr,
      transUnfold.indexing,
      vars = model.vars.toList() + listOf(locVar),
    )
  }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>
  ): Trace<CfaState<ExplState>, CfaAction> {
    return Trace.of(
      trace.states.map(this::valToState),
      trace.states.windowed(2, 1).map { (from, to) -> valToAction(from, to) },
    )
  }

  fun valToState(valuation: Valuation): CfaState<ExplState> {
    val locIndex = extractLocationIndex(valuation)
    return CfaState.of(
      locationIndexes.entries.first { it.value == locIndex }.key,
      ExplState.of(valuation), // TODO we should remove the loc variable from the valuation?
    )
  }

  fun valToAction(val1: Valuation, val2: Valuation): CfaAction {
    val locIndex1 = extractLocationIndex(val1)
    val locIndex2 = extractLocationIndex(val2)
    return CfaAction.create(
      indexedEdges[Pair(locIndex1, locIndex2)]
        ?: throw IllegalArgumentException("No edge found for the given location indices")
    )
  }

  fun extractLocationIndex(valuation: Valuation): Int {
    val valMap = valuation.toMap()
    Preconditions.checkArgument(
      valMap.containsKey(locVar),
      "State assigns no value to __loc__, this variable must be tracked explicitly!",
    )
    return (valMap[locVar] as IntLitExpr).value.toInt()
  }
}
