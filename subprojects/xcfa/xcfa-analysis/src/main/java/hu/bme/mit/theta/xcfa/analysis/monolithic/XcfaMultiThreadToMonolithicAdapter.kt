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
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState
import hu.bme.mit.theta.xcfa.analysis.XcfaProcessState.Companion.createLookup
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.util.*

class XcfaMultiThreadToMonolithicAdapter(
  model: XCFA,
  parseContext: ParseContext,
  private val initValues: Boolean = false,
) :
  XcfaToMonolithicAdapter(
    model.optimizeFurther(
      ProcedurePassManager(
        listOf(
          EliminateSelfLoops(),
          RemoveAbortBranchesPass(),
          LbePass(parseContext, LbePass.LbeLevel.LBE_LOCAL_FULL),
          RemoveUnnecessaryAtomicBlocksPass(),
          MutexToVarPass(),
        )
      )
    ),
    parseContext,
  ) {

  private lateinit var locVars: Map<StartLabel?, VarDecl<Type>>
  private val edgeVar = Decls.Var("__edge_", intType)
  private lateinit var locs: Map<StartLabel?, Map<XcfaLocation, Int>>
  private lateinit var edges: Map<StartLabel?, Map<XcfaEdge, Int>>
  private lateinit var threadIds: Map<StartLabel?, Int>

  override val monolithicExpr: MonolithicExpr
    get() {
      Preconditions.checkArgument(model.initProcedures.size == 1)
      val threads = model.staticThreadProcedureMap
      var pid = 0
      threadIds = threads.keys.associateWith { pid++ }
      val varLookUps =
        threadIds.entries.associate { (start, id) ->
          start to threads[start]!!.createLookup("T$id")
        }
      val pidVars =
        threads.keys.filterNotNull().associate {
          it.pidVar to Decls.Var(it.pidVar.changeVars(varLookUps[it]!!).name, intType)
        }
      locVars = threads.keys.associateWith { Decls.Var("__loc_t${threadIds[it]}", intType) }

      val locs = mutableMapOf<StartLabel?, MutableMap<XcfaLocation, Int>>()
      var locCounter = 0
      val edges = mutableMapOf<StartLabel?, MutableMap<XcfaEdge, Int>>()
      var edgeCounter = 0
      for ((s, proc) in threads) {
        val lm = locs.getOrPut(s) { mutableMapOf() }
        for (l in proc.locs) {
          lm[l] = locCounter++
        }

        val em = edges.getOrPut(s) { mutableMapOf() }
        for (e in proc.edges) {
          em[e] = edgeCounter++
        }
      }
      this.locs = locs
      this.edges = edges

      val tranList =
        threads.flatMap { (thread, proc) ->
          val locVar = locVars[thread]!!
          val locMap = locs[thread]!!
          val varLookUp = varLookUps[thread]!!
          proc.edges
            .map { edge: XcfaEdge ->
              val (source, target, label) = edge
              SequenceStmt.of(
                listOf(
                  AssumeStmt.of(Eq(locVar.ref, smtInt(locMap[source]!!))),
                  label.changeVars(varLookUp, parseContext).toStmt(),
                  AssignStmt.of(locVar, cast(smtInt(locMap[target]!!), locVar.type)),
                  AssignStmt.of(edgeVar, cast(smtInt(edges[thread]!![edge]!!), edgeVar.type)),
                ) +
                  label.getFlatLabels().flatMap { l ->
                    when (l) {
                      is StartLabel -> {
                        val pidVar = pidVars[l.pidVar]!!
                        val startedLocVar = locVars[l]!!
                        val startedLocMap = locs[l]!!
                        val startedInitLoc = threads[l]!!.initLoc
                        listOf(
                          AssumeStmt.of(Eq(startedLocVar.ref, smtInt(-1))),
                          AssignStmt.of(pidVar, cast(smtInt(threadIds[l]!!), pidVar.type)),
                          AssignStmt.of(
                            startedLocVar,
                            cast(smtInt(startedLocMap[startedInitLoc]!!), startedLocVar.type),
                          ),
                        )
                      }

                      is JoinLabel -> {
                        val pidVar = pidVars[l.pidVar]!!
                        val potentialJoinedThreads =
                          threadIds.entries.filter { (start, _) ->
                            start != null && pidVars[start.pidVar]!! == pidVar
                          }
                        val joinCondition =
                          if (potentialJoinedThreads.isEmpty())
                            error("No thread found for join with pid var ${l.pidVar}")
                          else {
                            And(
                              potentialJoinedThreads.map { (startLabel, pid) ->
                                val finalLoc = threads[startLabel]!!.finalLoc
                                Imply(
                                  Eq(pidVar.ref, smtInt(pid)),
                                  if (finalLoc.isPresent) {
                                    val joinedLocMap = locs[startLabel]!!
                                    val finalLocValue = joinedLocMap[finalLoc.get()]!!
                                    val joinedThreadLocVar = locVars[startLabel]!!
                                    Eq(joinedThreadLocVar.ref, smtInt(finalLocValue))
                                  } else {
                                    False()
                                  },
                                )
                              }
                            )
                          }
                        listOf(AssumeStmt.of(joinCondition))
                      }

                      else -> listOf()
                    }
                  }
              )
            }
            .toList() +
            if (proc.errorLoc.isPresent) {
              listOf(
                SequenceStmt.of(
                  listOf(
                    AssumeStmt.of(Eq(locVar.ref, smtInt(locMap[proc.errorLoc.get()]!!))),
                    AssignStmt.of(locVar, cast(smtInt(locMap[proc.errorLoc.get()]!!), locVar.type)),
                  )
                )
              )
            } else listOf()
        }

      val trans = NonDetStmt.of(tranList)
      val transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0))

      val locDefaultValues =
        threads
          .map { (thread, proc) ->
            if (thread == null) { // init procedure
              Eq(locVars[thread]!!.ref, smtInt(locs[thread]!![proc.initLoc]!!))
            } else {
              Eq(locVars[thread]!!.ref, smtInt(-1)) // -1 means thread has not started
            }
          }
          .let { And(it) }

      val edgeDefaultValue = Eq(edgeVar.ref, smtInt(-1))

      val defaultValues =
        if (initValues) trans.getDefaultValues(locVars.values + edgeVar) else True()

      val propExpr =
        threads
          .map { (thread, proc) ->
            if (proc.errorLoc.isPresent) {
              Neq(locVars[thread]!!.ref, smtInt(locs[thread]!![proc.errorLoc.get()]!!))
            } else {
              True()
            }
          }
          .let { And(it) }

      val events: List<Event<VarDecl<*>>> =
        threads
          .flatMap { (start, proc) ->
            proc.edges.flatMap { edge ->
              val varLookUp = varLookUps[start]!!
              edge.getFlatLabels().map { label ->
                label.toStmt().changeVars(varLookUp, parseContext).let {
                  if (label is StartLabel) {
                    val pidVar = pidVars[label.pidVar]!!
                    SequenceStmt.of(
                      listOf(
                        it,
                        AssignStmt.of(pidVar, cast(smtInt(threadIds[label]!!), pidVar.type)),
                      )
                    )
                  } else it
                }
              }
            }
          }
          .toSet()
          .map {
            object : Event<VarDecl<*>> {
              override fun getAffectedVars(): List<VarDecl<*>> =
                StmtUtils.getWrittenVars(it).toList()
            }
          }
          .toList()

      return MonolithicExpr(
        initExpr = And(locDefaultValues, edgeDefaultValue, defaultValues),
        transExpr = And(transUnfold.exprs),
        propExpr = propExpr,
        transOffsetIndex = transUnfold.indexing,
        vars = StmtUtils.getVars(trans).toList(),
        ctrlVars = locVars.values + edgeVar,
        events = events(tranList),
      )
    }

  override fun traceToModelTrace(
    trace: Trace<ExplState, ExprAction>
  ): Trace<XcfaState<PtrState<ExplState>>, XcfaAction> {
    return Trace.of(trace.states.map(this::valToState), trace.states.drop(1).map(this::valToAction))
  }

  override fun proofToModelProof(proof: InvariantProof): LocationInvariants {
    val result = mutableMapOf<XcfaLocation, Collection<ExprState>>()
    locs.entries
      .flatMap { (thread, locMap) ->
        val locVar = locVars[thread]!!
        locMap.entries.map { (loc, id) ->
          loc to
            listOf(
              PredState.of(
                ExprUtils.simplify(
                  proof.getInvariant(),
                  ImmutableValuation.builder().put(locVar, smtInt(id)).build(),
                )
              )
            )
        }
      }
      .forEach { (loc, states) ->
        if (loc in result) {
          val originalState = result[loc]!!.first()
          val newState = states.first()
          result[loc] =
            listOf(PredState.of(ExprUtils.simplify(Or(originalState.toExpr(), newState.toExpr()))))
        } else {
          result[loc] = states
        }
      }
    return LocationInvariants(result)
  }

  fun valToState(valuation: Valuation): XcfaState<PtrState<ExplState>> {
    val valMap = valuation.toMap()
    val processStates =
      locVars
        .mapNotNull { (thread, locVar) ->
          val locValue = valMap[locVar]?.value
          if (locValue == -1) return@mapNotNull null // thread not started
          val pid = threadIds[thread]!!
          val loc = locs[thread]!!.entries.find { (_, id) -> id == locValue }!!.key
          pid to XcfaProcessState(LinkedList(listOf(loc)), LinkedList())
        }
        .toMap()
    return XcfaState(
      model,
      processStates,
      PtrState(
        ExplState.of(
          ImmutableValuation.from(
            valuation.toMap().filter {
              it.key !in locVars.values &&
                it.key != edgeVar &&
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
    val edgeVarValue = valMap.entries.first { it.key == edgeVar }.value.value
    edges.forEach { (start, edgeMap) ->
      edgeMap.entries
        .find { (_, id) -> id == edgeVarValue }
        ?.let { (edge, _) ->
          return XcfaAction(pid = threadIds[start]!!, edge = edge)
        }
    }
    error("No edge found for edge id $edgeVarValue")
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
    check(
      nonLoopLabels.all { it is StmtLabel || it is StartLabel || it is JoinLabel || it is NopLabel }
    )
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
}
