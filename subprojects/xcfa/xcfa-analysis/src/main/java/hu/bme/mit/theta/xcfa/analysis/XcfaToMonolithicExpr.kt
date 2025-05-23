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
package hu.bme.mit.theta.xcfa.analysis

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CInt
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.*
import java.math.BigInteger
import java.util.*
import org.kframework.mpfr.BigFloat

private val LitExpr<*>.value: Int
  get() =
    when (this) {
      is IntLitExpr -> value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toInt()
      else -> error("Unknown integer type: $type")
    }

data class XcfaToMonolithicExprResult(
  val monolithicExpr: MonolithicExpr,
  val locVar: VarDecl<*>,
  val edgeVar: VarDecl<*>,
  val locMap: Map<XcfaLocation, Int>,
  val edgeMap: Map<XcfaEdge, Int>,
)

fun XCFA.toMonolithicExpr(
  parseContext: ParseContext,
  initValues: Boolean = false,
): XcfaToMonolithicExprResult {
  val intType = CInt.getUnsignedInt(parseContext).smtType

  fun int(value: Int): Expr<*> =
    when (intType) {
      is IntType -> Int(value)
      is BvType ->
        BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value.toLong()), intType.size)

      else -> error("Unknown integer type: $intType")
    }

  Preconditions.checkArgument(this.initProcedures.size == 1)
  val proc = this.initProcedures.stream().findFirst().orElse(null).first
  Preconditions.checkArgument(
    proc.edges.map { it.getFlatLabels() }.flatten().none { it !is StmtLabel }
  )
  //  Preconditions.checkArgument(proc.errorLoc.isPresent)

  val locMap = mutableMapOf<XcfaLocation, Int>()
  for ((i, x) in proc.locs.withIndex()) {
    locMap[x] = i
  }
  val edgeMap = mutableMapOf<XcfaEdge, Int>()
  for ((i, x) in proc.edges.withIndex()) {
    edgeMap[x] = i
  }
  val locVar = Decls.Var("__loc_", intType)
  val edgeVar = Decls.Var("__edge_", intType)
  val tranList =
    proc.edges
      .map { edge: XcfaEdge ->
        val (source, target, label) = edge
        SequenceStmt.of(
          listOf(
            AssumeStmt.of(Eq(locVar.ref, int(locMap[source]!!))),
            label.toStmt(),
            AssignStmt.of(locVar, cast(int(locMap[target]!!), locVar.type)),
            AssignStmt.of(edgeVar, cast(int(edgeMap[edge]!!), edgeVar.type)),
          )
        )
      }
      .toList()
  val trans = NonDetStmt.of(tranList)
  val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

  val defaultValues =
    if (initValues)
      StmtUtils.getVars(trans)
        .filter { !it.equals(locVar) and !it.equals(edgeVar) }
        .map {
          when (it.type) {
            is IntType -> Eq(it.ref, int(0))
            is BoolType -> Eq(it.ref, Bool(false))
            is BvType ->
              Eq(
                it.ref,
                BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, (it.type as BvType).size),
              )
            is RatType -> Eq(it.ref, Rat(0, 1))
            is FpType ->
              FpAssign(
                it.ref as Expr<FpType>,
                FpUtils.bigFloatToFpLitExpr(
                  BigFloat.zero((it.type as FpType).significand),
                  it.type as FpType,
                ),
              )
            else -> throw IllegalArgumentException("Unsupported type")
          }
        }
        .toList()
        .let { And(it) }
    else True()

  val monExpr =
    MonolithicExpr(
      initExpr =
        And(Eq(locVar.ref, int(locMap[proc.initLoc]!!)), Eq(edgeVar.ref, int(-1)), defaultValues),
      transExpr = And(transUnfold.exprs),
      propExpr =
        if (proc.errorLoc.isPresent) Neq(locVar.ref, int(locMap[proc.errorLoc.get()]!!))
        else True(),
      transOffsetIndex = transUnfold.indexing,
      vars =
        StmtUtils.getVars(trans).filter { !it.equals(locVar) and !it.equals(edgeVar) }.toList() +
          edgeVar +
          locVar,
      valToState = { valToState(it) },
      biValToAction = { val1, val2 -> valToAction(val1, val2) },
      ctrlVars = listOf(locVar, edgeVar),
    )
  return XcfaToMonolithicExprResult(monExpr, locVar, edgeVar, locMap, edgeMap)
}

fun XCFA.valToAction(val1: Valuation, val2: Valuation): XcfaAction {
  val val2Map = val2.toMap()
  val proc = this.procedures.first { it.name == "main" }
  val locMap = mutableMapOf<XcfaLocation, Int>()
  for ((i, x) in proc.locs.withIndex()) {
    locMap[x] = i
  }
  val edgeMap = mutableMapOf<XcfaEdge, Int>()
  for ((i, x) in proc.edges.withIndex()) {
    edgeMap[x] = i
  }
  return XcfaAction(
    pid = 0,
    edge =
      this.procedures
        .first { it.name == "main" }
        .edges
        .first { edge ->
          edgeMap[edge] == (val2Map[val2Map.keys.first { it.name == "__edge_" }]?.value ?: -1)
        },
  )
}

fun XCFA.valToState(val1: Valuation): XcfaState<PtrState<ExplState>> {
  val valMap = val1.toMap()
  val proc = this.procedures.first { it.name == "main" }
  val locMap = mutableMapOf<Int, XcfaLocation>()
  for ((i, x) in proc.locs.withIndex()) {
    locMap[i] = x
  }
  return XcfaState(
    this,
    locMap[(valMap[valMap.keys.first { it.name == "__loc_" }])?.value ?: -1]!!,
    PtrState(
      ExplState.of(
        ImmutableValuation.from(
          val1.toMap().filter {
            it.key.name != "__loc_" &&
              it.key.name != "__edge_" &&
              !it.key.name.startsWith("__temp_") &&
              !it.key.name.startsWith("__saved_")
          }
        )
      )
    ),
  )
}
