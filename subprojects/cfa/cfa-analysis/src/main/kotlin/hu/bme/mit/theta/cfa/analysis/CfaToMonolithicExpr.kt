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
package hu.bme.mit.theta.cfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.*
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import java.math.BigInteger
import java.util.*

fun CFA.toMonolithicExpr(): MonolithicExpr {
  Preconditions.checkArgument(this.errorLoc.isPresent)

  val map = mutableMapOf<CFA.Loc, Int>()
  for ((i, x) in this.locs.withIndex()) {
    map[x] = i
  }
  val locVar =
    Decls.Var(
      "__loc__",
      Int(),
    ) // TODO: add edge var as well, to avoid parallel edges causing problems
  val tranList =
    this.edges
      .map { e ->
        SequenceStmt.of(
          listOf(
            AssumeStmt.of(Eq(locVar.ref, Int(map[e.source]!!))),
            e.stmt,
            AssignStmt.of(locVar, Int(map[e.target]!!)),
          )
        )
      }
      .toList()

  val defaultValues =
    this.vars
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
  val initExpr = And(Eq(locVar.ref, Int(map[this.initLoc]!!)), defaultValues)
  val propExpr = Neq(locVar.ref, Int(map[this.errorLoc.orElseThrow()]!!))

  val offsetIndex = transUnfold.indexing

  return MonolithicExpr(
    initExpr,
    transExpr,
    propExpr,
    offsetIndex,
    vars = this.vars.toList() + listOf(locVar),
  )
}

fun CFA.valToAction(val1: Valuation, val2: Valuation): CfaAction {
  val val1Map = val1.toMap()
  val val2Map = val2.toMap()
  var i = 0
  val map: MutableMap<CFA.Loc, Int> = mutableMapOf()
  for (x in this.locs) {
    map[x] = i++
  }
  return CfaAction.create(
    this.edges.first { edge ->
      map[edge.source] ==
        (val1Map[val1Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt() &&
        map[edge.target] ==
          (val2Map[val2Map.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()
    }
  )
}

fun CFA.valToState(val1: Valuation): CfaState<ExplState> {
  val valMap = val1.toMap()
  var i = 0
  val map: MutableMap<Int, CFA.Loc> = mutableMapOf()
  for (x in this.locs) {
    map[i++] = x
  }
  return CfaState.of(
    map[(valMap[valMap.keys.first { it.name == "__loc_" }] as IntLitExpr).value.toInt()],
    ExplState.of(val1),
  )
}
