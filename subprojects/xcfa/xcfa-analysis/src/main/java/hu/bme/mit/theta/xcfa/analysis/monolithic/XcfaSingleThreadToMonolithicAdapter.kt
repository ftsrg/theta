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
package hu.bme.mit.theta.xcfa.analysis.monolithic

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.ModelToMonolithicAdapter
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.pred.PredState
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
import hu.bme.mit.theta.core.type.Type
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
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CInt
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.kframework.mpfr.BigFloat
import java.math.BigInteger

private val LitExpr<*>.value: Int
  get() =
    when (this) {
      is IntLitExpr -> value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(this).toInt()
      else -> error("Unknown integer type: $type")
    }

class XcfaSingleThreadToMonolithicAdapter(
  override val model: XCFA,
  private val parseContext: ParseContext,
  private val initValues: Boolean = false
) :
  ModelToMonolithicAdapter<XCFA, XcfaState<PtrState<ExplState>>, XcfaAction, LocationInvariants> {

  private lateinit var locVar: VarDecl<Type>
  private lateinit var locations: List<XcfaLocation>
  private lateinit var edges: List<XcfaEdge>
  private lateinit var smtAwareInteger: (Int) -> LitExpr<*>

  override val monolithicExpr: MonolithicExpr get() {
    val intType = CInt.getUnsignedInt(parseContext).smtType

    smtAwareInteger =
      fun(value: Int): LitExpr<*> =
        when (intType) {
          is IntType -> Int(value)
          is BvType ->
            BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value.toLong()), intType.size)

          else -> error("Unknown integer type: $intType")
        }

    Preconditions.checkArgument(model.initProcedures.size == 1)
    val proc = model.initProcedures.stream().findFirst().orElse(null).first
    Preconditions.checkArgument(
      proc.edges.map { it.getFlatLabels() }.flatten().none { it !is StmtLabel }
    )

    locations = proc.locs.toList()
    edges = proc.edges.toList()
    val locationMap = locations.mapIndexed { index, location -> location to index }.toMap()
    val edgeMap = edges.mapIndexed { index, edge -> edge to index }.toMap()
    locVar = Decls.Var("__loc_", intType)
    val edgeVar = Decls.Var("__edge_", intType)
    val tranList =
      proc.edges
        .map { edge: XcfaEdge ->
          val (source, target, label) = edge
          SequenceStmt.of(
            listOf(
              AssumeStmt.of(Eq(locVar.ref, smtAwareInteger(locationMap[source]!!))),
              label.toStmt(),
              AssignStmt.of(locVar, cast(smtAwareInteger(locationMap[target]!!), locVar.type)),
              AssignStmt.of(edgeVar, cast(smtAwareInteger(edgeMap[edge]!!), edgeVar.type)),
            )
          )
        }
        .toList()
    val trans = NonDetStmt.of(tranList)
    val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

    val defaultValues =
      if (initValues)
        StmtUtils.getVars(trans)
          .filter { (it != (locVar)) and (it != (edgeVar)) }
          .map {
            when (it.type) {
              is IntType -> Eq(it.ref, smtAwareInteger(0))
              is BoolType -> Eq(it.ref, Bool(false))
              is BvType ->
                Eq(
                  it.ref,
                  BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, (it.type as BvType).size),
                )
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

    return MonolithicExpr(
      initExpr =
        And(
          Eq(locVar.ref, smtAwareInteger(locationMap[proc.initLoc]!!)),
          Eq(edgeVar.ref, smtAwareInteger(-1)),
          defaultValues,
        ),
      transExpr = And(transUnfold.exprs),
      propExpr =
        if (proc.errorLoc.isPresent)
          Neq(locVar.ref, smtAwareInteger(locationMap[proc.errorLoc.get()]!!))
        else True(),
      transOffsetIndex = transUnfold.indexing,
      vars =
        StmtUtils.getVars(trans).filter { (it != (locVar)) and (it != (edgeVar)) }.toList() +
          edgeVar +
          locVar,
      ctrlVars = listOf(locVar, edgeVar),
    )
  }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>,
  ): Trace<XcfaState<PtrState<ExplState>>, XcfaAction> {
    return Trace.of(
      trace.states.map(this::valToState),
      trace.states.drop(1).map(this::valToAction)
    )
  }

  override fun proofToModelProof(proof: InvariantProof): LocationInvariants =
    LocationInvariants(
      locations
        .mapIndexed { index, location ->
          Pair(
            location,
            listOf(
              PredState.of(
                ExprUtils.simplify(
                  proof.getInvariant(),
                  ImmutableValuation.builder().put(locVar, smtAwareInteger(index)).build(),
                )
              )
            ),
          )
        }
        .toMap()
    )

  fun valToState(valuation: Valuation): XcfaState<PtrState<ExplState>> {
    val valMap = valuation.toMap()
    return XcfaState(
      model,
      locations[(valMap[valMap.keys.first { it.name == "__loc_" }])!!.value],
      PtrState(
        ExplState.of(
          ImmutableValuation.from(
            valuation.toMap().filter {
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

  /**
   * Converts the target valuation to an action. The valuation must contain the edge index in the
   * `__edge_` variable.
   */
  fun valToAction(valuation: Valuation): XcfaAction {
    val valMap = valuation.toMap()
    return XcfaAction(
      pid = 0,
      edge = edges[valMap.entries.first { it.key.name == "__edge_" }.value.value],
    )
  }
}
