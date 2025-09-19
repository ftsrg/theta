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
import hu.bme.mit.theta.xcfa.passes.*
import org.kframework.mpfr.BigFloat
import java.math.BigInteger
import java.util.*

private val LitExpr<*>.value: Int
  get() =
    when (this) {
      is IntLitExpr -> value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toInt()
      else -> error("Unknown integer type: $type")
    }

data class XcfaToMonolithicExprResult(
  val monolithicExpr: MonolithicExpr,
  val locVars: Collection<VarDecl<*>>,
  val edgeVars: Collection<VarDecl<*>>,
  val locMap: Map<XcfaLocation, Int>,
  val edgeMap: Map<XcfaEdge, Int>,
)

fun XCFA.toMonolithicExpr(
  parseContext: ParseContext,
  initValues: Boolean = false,
): XcfaToMonolithicExprResult = convertToMonolithicExpr(this, parseContext, initValues)

private fun convertToMonolithicExpr(
  originalXcfa: XCFA,
  parseContext: ParseContext,
  initValues: Boolean = false,
): XcfaToMonolithicExprResult {
  val xcfa = originalXcfa.optimizeFurther(
    ProcedurePassManager(
      listOf(
        EliminateSelfLoops(),
        RemoveAbortBranchesPass(),
        LbePass(parseContext, LbePass.LbeLevel.LBE_LOCAL_FULL),
        RemoveUnnecessaryAtomicBlocksPass(),
        MutexToVarPass(),
      )
    )
  )
  val intType = CInt.getUnsignedInt(parseContext).smtType

  fun int(value: Int): Expr<*> =
    when (intType) {
      is IntType -> Int(value)
      is BvType ->
        BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value.toLong()), intType.size)

      else -> error("Unknown integer type: $intType")
    }

  Preconditions.checkArgument(xcfa.initProcedures.size == 1)
  val threads = xcfa.staticThreadProcedureMap
  var pid = 0
  val threadIds = threads.keys.associateWith { pid++ }

  val locMap = mutableMapOf<XcfaLocation, Int>()
  for ((_, proc) in threads) {
    for ((i, x) in proc.locs.withIndex()) {
      locMap[x] = i
    }
  }
  val edgeMap = mutableMapOf<XcfaEdge, Int>()
  for ((_, proc) in threads) {
    for ((i, x) in proc.edges.withIndex()) {
      edgeMap[x] = i
    }
  }

  val locVars = threads.keys.associateWith { Decls.Var("__loc_t${threadIds[it]}", intType) }
  val edgeVars = threads.keys.associateWith { Decls.Var("__edge_t${threadIds[it]}", intType) }

  val tranList =
    threads.flatMap { (label, proc) ->
      val locVar = locVars[label]!!
      val edgeVar = edgeVars[label]!!
      proc.edges
        .map { edge: XcfaEdge ->
          val (source, target, label) = edge
          SequenceStmt.of(
            listOf(
              AssumeStmt.of(Eq(locVar.ref, int(locMap[source]!!))),
              label.toStmt(),
              AssignStmt.of(locVar, cast(int(locMap[target]!!), locVar.type)),
              AssignStmt.of(edgeVar, cast(int(edgeMap[edge]!!), edgeVar.type)),
            ) +
              if (label is StartLabel) {
                val startedLocVar = locVars[label]!!
                val startedInitLoc = threads[label]!!.initLoc
                listOf(
                  AssumeStmt.of(Eq(startedLocVar.ref, int(-1))),
                  AssignStmt.of(
                    startedLocVar,
                    cast(int(locMap[startedInitLoc]!!), startedLocVar.type),
                  ),
                )
              } else listOf()
          )
        }
        .toList() +
        if (proc.errorLoc.isPresent) {
          listOf(
            SequenceStmt.of(
              listOf(
                AssumeStmt.of(Eq(locVar.ref, int(locMap[proc.errorLoc.get()]!!))),
                AssignStmt.of(locVar, cast(int(locMap[proc.errorLoc.get()]!!), locVar.type)),
              )
            )
          )
        } else listOf()
    }
  val trans = NonDetStmt.of(tranList)
  val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

  val locDefaultValues =
    threads
      .map { (label, proc) ->
        if (label == null) { // init procedure
          Eq(locVars[label]!!.ref, int(locMap[proc.initLoc]!!))
        } else {
          Eq(locVars[label]!!.ref, int(-1)) // -1 means thread has not started yet
        }
      }
      .let { And(it) }

  val edgeDefaultValues = edgeVars.values.map { Eq(it.ref, int(-1)) }.let { And(it) }

  val defaultValues =
    if (initValues)
      StmtUtils.getVars(trans)
        .filter { it !in locVars.values && it !in edgeVars.values }
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

  val propExpr =
    threads
      .map { (label, proc) ->
        if (proc.errorLoc.isPresent) Neq(locVars[label]!!.ref, int(locMap[proc.errorLoc.get()]!!))
        else True()
      }
      .let { And(it) }

  val monExpr =
    MonolithicExpr(
      initExpr = And(locDefaultValues, edgeDefaultValues, defaultValues),
      transExpr = And(transUnfold.exprs),
      propExpr = propExpr,
      transOffsetIndex = transUnfold.indexing,
      vars =
        StmtUtils.getVars(trans).filter { it !in locVars.values && it !in edgeVars.values } +
          edgeVars.values +
          locVars.values,
      valToState = { xcfa.valToState(it) },
      biValToAction = { val1, val2 -> xcfa.valToAction(val1, val2) },
      ctrlVars = locVars.values + edgeVars.values,
    )
  return XcfaToMonolithicExprResult(monExpr, locVars.values, edgeVars.values, locMap, edgeMap)
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

private val XCFA.staticThreadProcedureMap: Map<StartLabel?, XcfaProcedure>
  get() {
    val initProc = this.initProcedures.first().first
    return mapOf(null to initProc) + staticThreadProcedureMap(setOf(initProc))
  }

private fun XCFA.staticThreadProcedureMap(
  startedProcedures: Set<XcfaProcedure>
): Map<StartLabel, XcfaProcedure> {
  val procedure = startedProcedures.last()
  val loopEdges = procedure.loopEdges
  check(loopEdges.all { edge -> edge.getFlatLabels().all { it is StmtLabel || it is NopLabel } })
  val nonLoopEdges = procedure.edges - loopEdges
  val nonLoopLabels = nonLoopEdges.flatMap { it.getFlatLabels() }
  check(nonLoopLabels.all { it is StmtLabel || it is StartLabel || it is JoinLabel || it is NopLabel })
  val startLabels = nonLoopLabels.filterIsInstance<StartLabel>()

  val threads = mutableMapOf<StartLabel, XcfaProcedure>()
  startLabels.forEach { startLabel ->
    val startedProcedure = procedures.find { it.name == startLabel.name }!!
    check(startedProcedure !in startedProcedures) {
      "Recursion is not allowed in static thread-procedure mapping!"
    }
    threads[startLabel] = startedProcedure
    threads.putAll(staticThreadProcedureMap(startedProcedures + startedProcedure))
  }
  return threads
}

private val XcfaProcedure.loopEdges: Set<XcfaEdge>
  get() {
    val loopEdges = mutableSetOf<XcfaEdge>()
    val visited = mutableSetOf<XcfaLocation>()
    val stack = Stack<XcfaLocation>()
    stack.push(this.initLoc)
    while (stack.isNotEmpty()) {
      val loc = stack.pop()
      if (!visited.add(loc)) continue
      for (edge in loc.outgoingEdges) {
        if (edge.target in stack) {
          val (_, es) = getLoopElements(edge)
          loopEdges.addAll(es)
        } else {
          stack.push(edge.target)
        }
      }
    }
    return loopEdges
  }
