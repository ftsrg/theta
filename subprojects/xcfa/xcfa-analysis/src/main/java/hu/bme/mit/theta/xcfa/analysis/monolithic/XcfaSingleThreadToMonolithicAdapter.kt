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
package hu.bme.mit.theta.xcfa.analysis.monolithic

import com.google.common.base.Preconditions
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.InvariantProof
import hu.bme.mit.theta.analysis.algorithm.TransitionInvariantProof
import hu.bme.mit.theta.analysis.algorithm.bounded.LivenessWitness
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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.ErrorDetection.TERMINATION
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.passes.DereferenceToArrayPass
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.InvariantCheckMetaData
import hu.bme.mit.theta.xcfa.witnesses.UndefinedBehaviorMetaData

class XcfaSingleThreadToMonolithicAdapter
private constructor(
  model: XCFA,
  property: XcfaProperty,
  parseContext: ParseContext,
  initValues: Boolean,
  private val blocks: BlockEncoding?,
) :
  XcfaToMonolithicAdapter(
    model,
    property,
    ProcedurePassManager(listOf(DereferenceToArrayPass()) + (blocks?.passes ?: listOf())),
    parseContext,
    initValues,
  ) {

  /** [blockEncoding]: one transition per block instead of per edge (see [BlockEncoding]). */
  @JvmOverloads
  constructor(
    model: XCFA,
    property: XcfaProperty,
    parseContext: ParseContext,
    initValues: Boolean = false,
    blockEncoding: Boolean = false,
  ) : this(
    model,
    property,
    parseContext,
    initValues,
    if (blockEncoding && property.verifiedProperty == ERROR_LOCATION && onlyLocalLabels(model))
      BlockEncoding(parseContext)
    else null,
  )

  private lateinit var locVar: VarDecl<Type>
  private val edgeVar = Decls.Var("__edge_", intType)
  private lateinit var locations: List<XcfaLocation>
  private lateinit var edges: List<XcfaEdge>

  override val monolithicExpr: MonolithicExpr
    get() {
      Preconditions.checkArgument(model.initProcedures.size == 1)
      val proc = model.initProcedures.stream().findFirst().orElse(null).first
      Preconditions.checkArgument(
        proc.edges.flatMap { it.getAllLabels() }.none { it !is StmtLabel && it !is NopLabel }
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
          if (property.verifiedProperty != TERMINATION && proc.errorLoc.isPresent)
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
      val vars = StmtUtils.getVars(trans).toList()

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
            property.verifiedProperty == TERMINATION -> model.initProcedures[0].first.prop
            proc.errorLoc.isPresent -> Neq(locVar.ref, smtInt(locationMap[proc.errorLoc.get()]!!))
            else -> True()
          },
        transOffsetIndex = transUnfold.indexing,
        vars = vars,
        ctrlVars = listOf(locVar, edgeVar),
        events = events(tranList),
        livenessWitness = livenessWitness(vars.toSet()),
      )
    }

  /** The invariants of a termination witness, checked at the locations that carry them. */
  private fun livenessWitness(modelVars: Set<VarDecl<*>>): LivenessWitness? {
    val checks =
      locations.flatMapIndexed { index, location ->
        (location.metadata as? InvariantCheckMetaData)?.checks.orEmpty().map { index to it }
      }
    val undefinedBehavior =
      locations.indices.filter { locations[it].metadata == UndefinedBehaviorMetaData }
    if (checks.isEmpty() && undefinedBehavior.isEmpty()) return null
    check(property.verifiedProperty == TERMINATION) {
      "Witness invariants are checked only for termination"
    }
    fun at(variable: VarDecl<*>, indices: List<Int>) =
      Or(indices.map { Eq(variable.ref, smtInt(it)) })

    val stateInvariant =
      And(
        checks
          .filter { !it.second.isTransition }
          .map { (index, check) -> Imply(at(locVar, listOf(index)), check.expr) }
      )
    val prevLocVar = Decls.Var("__theta_anyprev___loc_", locVar.type)
    val transitions = checks.filter { it.second.isTransition }.groupBy { it.second.entry }
    val transitionInvariant =
      And(
        transitions.values.map { group ->
          // Any two visits of the evaluation point are related, whichever of its locations they are
          // at
          val first = group.first().second
          check(group.all { it.second == first }) {
            "A transition invariant over variables of different scopes is not supported"
          }
          val indices = group.map { it.first }
          Imply(And(at(locVar, indices), at(prevLocVar, indices)), first.expr)
        }
      )
    val anyPrev =
      checks.flatMap { it.second.anyPrev.entries }.associate { it.toPair() } +
        (prevLocVar to locVar)
    val unknown =
      (ExprUtils.getVars(stateInvariant) + ExprUtils.getVars(transitionInvariant) - anyPrev.keys)
        .filter { it !in modelVars }
    check(unknown.isEmpty()) { "Witness invariants over variables not in the model: $unknown" }
    val saveAt =
      cycleCover(transitions.values.flatten().map { locations[it.first] }.toSet()).map {
        locations.indexOf(it)
      }
    return LivenessWitness(
      stateInvariant,
      transitionInvariant,
      anyPrev,
      at(locVar, saveAt),
      at(locVar, undefinedBehavior),
    )
  }

  /**
   * [required] and, for each cycle without these, the target of a back edge of a depth-first search
   * on it. Every cycle passes a location of the result, so every infinite run visits one infinitely
   * often.
   */
  private fun cycleCover(required: Set<XcfaLocation>): Set<XcfaLocation> {
    val successors = edges.groupBy({ it.source }, { it.target })
    val cover = LinkedHashSet(required)
    val visited = HashSet(required)
    val onPath = HashSet<XcfaLocation>()
    for (root in locations) {
      if (!visited.add(root)) continue
      val path = ArrayDeque(listOf(root to successors[root].orEmpty().iterator()))
      onPath += root
      while (path.isNotEmpty()) {
        val (location, next) = path.last()
        if (!next.hasNext()) {
          path.removeLast()
          onPath -= location
          continue
        }
        val successor = next.next()
        if (successor in onPath) cover += successor
        else if (visited.add(successor)) {
          path.addLast(successor to successors[successor].orEmpty().iterator())
          onPath += successor
        }
      }
    }
    return cover
  }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>
  ): Trace<XcfaState<PtrState<ExplState>>, XcfaAction> {
    return Trace.of(trace.states.map(this::valToState), trace.states.drop(1).map(this::valToAction))
  }

  override fun proofToModelProof(proof: InvariantProof): LocationInvariants {
    if (proof is TransitionInvariantProof) return transitionProofToModelProof(proof)
    return LocationInvariants(
      locations
        .mapIndexed { index, location ->
          Pair(
            location,
            listOf(
              PredState.of(
                withoutChoices(
                  ExprUtils.simplify(
                    proof.getInvariant(),
                    ImmutableValuation.builder().put(locVar, smtInt(index)).build(),
                  )
                )
              )
            ),
          )
        }
        .toMap()
    )
  }

  /**
   * The earlier state is at the same location, so both edge variables hold the index of an incoming
   * edge of that location; they are eliminated by enumerating these indices.
   */
  private fun transitionProofToModelProof(proof: TransitionInvariantProof): LocationInvariants {
    // Earlier values keep the C name of their variable and are printed as \at(x, AnyPrev)
    proof.anyPrev.forEach { (decl, prev) ->
      parseContext.metadata.getMetadataValue(decl.name, "cName").ifPresent {
        parseContext.metadata.create(prev.name, "cName", it)
        parseContext.metadata.create(prev.name, "isAnyPrev", true)
      }
    }
    val prevLocVar = proof.anyPrev.getValue(locVar)
    val prevEdgeVar = proof.anyPrev.getValue(edgeVar)
    return LocationInvariants(
      locations
        .mapIndexed { index, location ->
          val edgeIndices =
            location.incomingEdges.map(edges::indexOf) +
              if (location.initial) listOf(-1) else listOf()
          val invariant =
            Or(
              edgeIndices.flatMap { edge ->
                edgeIndices.map { prevEdge ->
                  ExprUtils.simplify(
                    proof.getInvariant(),
                    ImmutableValuation.builder()
                      .put(locVar, smtInt(index))
                      .put(prevLocVar, smtInt(index))
                      .put(edgeVar, smtInt(edge))
                      .put(prevEdgeVar, smtInt(prevEdge))
                      .build(),
                  )
                }
              }
            )
          Pair(location, listOf(PredState.of(withoutChoices(ExprUtils.simplify(invariant)))))
        }
        .toMap(),
      true,
    )
  }

  /**
   * A choice variable of the block encoding is no program variable: such an invariant is dropped.
   */
  private fun withoutChoices(invariant: Expr<BoolType>): Expr<BoolType> =
    if (ExprUtils.getVars(invariant).any { BlockEncoding.CHOICE_PREFIX in it.name }) True()
    else invariant

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
                !it.key.name.startsWith("__saved_") &&
                !it.key.name.startsWith(BlockEncoding.CHOICE_PREFIX)
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
    val edge = edges[valMap.entries.first { it.key.name == "__edge_" }.value.value]
    if (blocks == null) return XcfaAction(pid = 0, edge = edge)
    val procedure = model.initProcedures.first().first.name
    return XcfaAction(
      0,
      edge.source,
      edge.target,
      blocks.expand(procedure, edge, valuation),
      edge.metadata,
    )
  }
}

/** Block encoding drops edges that cannot reach the error, so every label must be local. */
private fun onlyLocalLabels(model: XCFA): Boolean =
  model.initProcedures.singleOrNull()?.first?.edges?.all { edge ->
    edge.getAllLabels().all { it is StmtLabel || it is NopLabel }
  } == true
