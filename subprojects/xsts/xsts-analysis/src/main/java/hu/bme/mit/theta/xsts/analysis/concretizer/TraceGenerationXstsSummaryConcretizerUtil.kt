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
package hu.bme.mit.theta.xsts.analysis.concretizer

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.*
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.refinement.ExprSummaryFwBinItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xsts.XSTS
import hu.bme.mit.theta.xsts.analysis.XstsAction
import hu.bme.mit.theta.xsts.analysis.XstsState
import java.util.*
import java.util.stream.Collectors

object TraceGenerationXstsSummaryConcretizerUtil {

  private val infeasibles: MutableList<Tuple2<List<XstsState<ExplState>>, ItpRefutation>> =
    ArrayList()
  var report: String? = null
    private set

  private var foundInfeasible = false

  fun concretize(
    summary: AbstractTraceSummary<XstsState<*>, XstsAction>,
    solverFactory: SolverFactory,
    xsts: XSTS,
  ): Map<AbstractSummaryNode<out XstsState<*>, out XstsAction>, XstsState<ExplState>> {
    val varFilter = VarFilter.of(xsts)
    val checker: ExprSummaryFwBinItpChecker =
      ExprSummaryFwBinItpChecker.create(xsts.initFormula, solverFactory.createItpSolver())
    val status = checker.check(summary)

    checkState(status.feasible, "Summary could not be concretized")

    val concreteSummary = (status as FeasibleExprSummaryStatus<XstsState<*>, XstsAction>).summary

    val xstsStateMap:
      MutableMap<AbstractSummaryNode<out XstsState<*>, out XstsAction>, XstsState<ExplState>> =
      mutableMapOf()
    for ((abstractNode, valuation) in concreteSummary.valuationMap) {
      xstsStateMap[abstractNode] =
        XstsState.of<ExplState>(
          ExplState.of(varFilter.filter(valuation)),
          abstractNode.getStates().iterator().next().lastActionWasEnv(),
          abstractNode.getStates().iterator().next().isInitialized(),
        )
    }

    return xstsStateMap
  }

  private fun addToReport(
    refutation: ItpRefutation,
    abstractTrace: Trace<XstsState<ExplState>, XstsAction>,
  ) {
    val prunedStates = ArrayList<XstsState<ExplState>>()
    for (i in refutation.pruneIndex + 1 until abstractTrace.states.size) {
      if (
        abstractTrace.getState(i).toString().contains("last_internal")
      ) { // xsts specific condition
        prunedStates.add(abstractTrace.getState(i))
      }
    }
    infeasibles.add(Tuple2.of(prunedStates, refutation))
  }

  private fun createReport(traces: Collection<Trace<XstsState<ExplState>, XstsAction>>) {
    var statesVisited =
      traces
        .stream()
        .map { obj: Trace<XstsState<ExplState>, XstsAction> -> obj.states }
        .flatMap { obj: List<XstsState<ExplState>> -> obj.stream() }
        .collect(Collectors.toSet())
    // xsts specific part
    statesVisited =
      statesVisited
        .stream()
        .filter { state: XstsState<ExplState> -> state.toString().contains("last_internal") }
        .collect(Collectors.toSet())

    val missingStates: MutableList<XstsState<ExplState>> = ArrayList()
    val stateRefutations: MutableList<ItpRefutation> = ArrayList()
    for (infeasible in infeasibles) {
      var missingState = false
      for (xstsState in infeasible.get1()) {
        if (!stateContains(statesVisited, xstsState)) {
          missingState = true
          missingStates.add(xstsState)
        }
      }
      if (missingState) {
        stateRefutations.add(infeasible.get2())
      }
    }

    val problematicVariables =
      stateRefutations
        .stream()
        .map { refutation: ItpRefutation -> ExprUtils.getVars(refutation[refutation.pruneIndex]) }
        .flatMap { obj: Set<VarDecl<*>> -> obj.stream() }
        .collect(Collectors.toSet())

    val reportBuilder = StringBuilder()

    // allapot fedest pontosan nezzuk, transition fedest csak annyira, hogy serulhetett-e
    if (foundInfeasible) {
      reportBuilder.append(
        "There were infeasible traces found; transition coverage might be incomplete\n"
      )
    } else {
      reportBuilder.append("Trace coverage is complete\n")
    }

    if (stateRefutations.isEmpty()) {
      reportBuilder.append("State coverage (including variables in variable list) is complete\n")
    } else {
      reportBuilder.append(
        "State coverage (including variables in variable list) is incomplete.\n\n"
      )

      reportBuilder.append(
        "The following abstract states are not covered (they might or might not be possible):\n"
      )

      for (missingState in missingStates) {
        reportBuilder.append(missingState.toString())
        reportBuilder.append("\n------------------------------\n")
      }

      reportBuilder.append("\n")
      // TODO ez NAGYON heurisztika, pl ha prioritas miatt maradt ki valami, akkor hulyesegeket is
      // mondhat
      reportBuilder.append(
        "Maybe adding some of the following variables to the variable list can help:\n"
      )
      reportBuilder.append(
        problematicVariables
          .stream()
          .map { obj: VarDecl<*> -> obj.name }
          .collect(Collectors.toSet())
      )
      reportBuilder.append("\n")
    }

    report = reportBuilder.toString()
  }

  private fun stateContains(
    statesVisited: Set<XstsState<ExplState>>,
    xstsState: XstsState<ExplState>,
  ): Boolean {
    val sb1 = StringBuilder()
    val stateLineList =
      Arrays.asList(
        *xstsState.toString().split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
      )
    for (line in stateLineList) {
      if (!line.contains("__id_")) {
        sb1.append(line)
        sb1.append("\n")
      }
    }
    val xstsStateNoTransitions = sb1.toString()

    val statesVisitedNoTransitions =
      statesVisited
        .stream()
        .map { state: XstsState<ExplState> ->
          val sb = StringBuilder()
          val lineList =
            Arrays.asList(
              *state.toString().split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
            )
          for (line in lineList) {
            if (!line.contains("__id_")) {
              sb.append(line)
              sb.append("\n")
            }
          }
          sb.toString()
        }
        .toList()

    return statesVisitedNoTransitions.contains(xstsStateNoTransitions)
  }

  private fun shortenTrace(
    abstractTrace: Trace<XstsState<ExplState>, XstsAction>,
    pruneIndex: Int,
  ): Trace<XstsState<ExplState>, XstsAction> {
    var abstractTrace = abstractTrace
    var newStates: List<XstsState<ExplState>> = ArrayList(abstractTrace.states)
    newStates = newStates.subList(0, pruneIndex + 1)
    var newActions: List<XstsAction> = ArrayList(abstractTrace.actions)
    newActions = newActions.subList(0, pruneIndex)
    abstractTrace = Trace.of(newStates, newActions) // remove last state
    return abstractTrace
  }
}
