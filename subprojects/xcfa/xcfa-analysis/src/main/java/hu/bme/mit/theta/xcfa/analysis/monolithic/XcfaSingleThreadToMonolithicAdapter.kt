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
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.passes.DereferenceToArrayPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class XcfaSingleThreadToMonolithicAdapter(
  model: XCFA,
  property: ErrorDetection,
  parseContext: ParseContext,
  initValues: Boolean = false,
) :
  XcfaToMonolithicAdapter(
    model,
    property,
    ProcedurePassManager(listOf(DereferenceToArrayPass())),
    parseContext,
    initValues,
  ) {

  private lateinit var locVar: VarDecl<Type>
  private val edgeVar = Decls.Var("__edge_", intType)
  private lateinit var locations: List<XcfaLocation>
  private lateinit var edges: List<XcfaEdge>

  override val monolithicExpr: MonolithicExpr
    get() {
      Preconditions.checkArgument(model.initProcedures.size == 1)
      val proc = model.initProcedures.stream().findFirst().orElse(null).first
      Preconditions.checkArgument(
        proc.edges.map { it.getFlatLabels() }.flatten().none { it !is StmtLabel }
      )

      // Initialize location var, location and edge mappings
      locations = proc.locs.toList()
      edges = proc.edges.toList()
      val locationMap = locations.mapIndexed { index, location -> location to index }.toMap()
      val edgeMap = edges.mapIndexed { index, edge -> edge to index }.toMap()
      locVar = Decls.Var("__loc_", intType)

      // Build transition list
      val tranList =
        proc.edges.map { edge: XcfaEdge ->
          val (source, target, label) = edge
          SequenceStmt.of(
            listOf(
              AssumeStmt.of(Eq(locVar.ref, smtInt(locationMap[source]!!))),
              label.toStmt(),
              AssignStmt.of(locVar, cast(smtInt(locationMap[target]!!), locVar.type)),
              AssignStmt.of(edgeVar, cast(smtInt(edgeMap[edge]!!), edgeVar.type)),
            )
          )
        } +
          if (property != ErrorDetection.TERMINATION && proc.errorLoc.isPresent)
            proc.errorLoc.get().let { errorLoc ->
              listOf(
                SequenceStmt.of(
                  listOf(
                    AssumeStmt.of(Eq(locVar.ref, smtInt(locationMap[errorLoc]!!))),
                    AssignStmt.of(locVar, cast(smtInt(locationMap[errorLoc]!!), locVar.type)),
                  )
                )
              )
            }
          else listOf()
      val trans = NonDetStmt.of(tranList)
      val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

      // Build initializer expressions
      val defaultValues = if (initValues) trans.getDefaultValues(setOf(locVar, edgeVar)) else True()

      // Build monolithic expression
      return MonolithicExpr(
        initExpr =
          And(
            Eq(locVar.ref, smtInt(locationMap[proc.initLoc]!!)),
            Eq(edgeVar.ref, smtInt(-1)),
            defaultValues,
          ),
        transExpr = And(transUnfold.exprs),
        propExpr =
          when {
            property == ErrorDetection.TERMINATION -> model.initProcedures[0].first.prop
            proc.errorLoc.isPresent -> Neq(locVar.ref, smtInt(locationMap[proc.errorLoc.get()]!!))
            else -> True()
          },
        transOffsetIndex = transUnfold.indexing,
        vars = StmtUtils.getVars(trans).toList(),
        ctrlVars = listOf(locVar, edgeVar),
        events = events(tranList),
      )
    }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>
  ): Trace<XcfaState<PtrState<ExplState>>, XcfaAction> {
    return Trace.of(trace.states.map(this::valToState), trace.states.drop(1).map(this::valToAction))
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
                  ImmutableValuation.builder().put(locVar, smtInt(index)).build(),
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
