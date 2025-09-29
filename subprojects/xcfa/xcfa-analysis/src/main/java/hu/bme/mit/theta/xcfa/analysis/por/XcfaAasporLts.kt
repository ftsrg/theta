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
package hu.bme.mit.theta.xcfa.analysis.por

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.XCFA

open class XcfaAasporLts(
  xcfa: XCFA,
  private val ignoredVarRegistry: MutableMap<VarDecl<*>, MutableSet<ExprState>>,
) : XcfaSporLts(xcfa) {

  override fun <P : Prec> getEnabledActionsFor(
    state: XcfaState<out PtrState<*>>,
    exploredActions: Collection<XcfaAction>,
    prec: P,
  ): Set<XcfaAction> {
    // Collecting enabled actions
    val allEnabledActions = simpleXcfaLts.getEnabledActionsFor(state, exploredActions, prec)

    // Calculating the source set starting from every (or some of the) enabled transition or from
    // exploredActions if it is not empty
    // The minimal source set is stored
    var minimalSourceSet = mutableSetOf<XcfaAction>()
    val sourceSetFirstActions =
      if (exploredActions.isEmpty()) {
        getSourceSetFirstActions(state, allEnabledActions)
      } else {
        setOf(exploredActions)
      }
    var finalIgnoredVars = setOf<VarDecl<*>>()

    // Calculate source sets from all possible starting action set
    for (firstActions in sourceSetFirstActions) {
      // Variables that have been ignored (if they would be in the precision, more actions have had
      // to be added to the source set)
      val ignoredVars = mutableSetOf<VarDecl<*>>()
      val sourceSet = calculateSourceSet(state, allEnabledActions, firstActions, prec, ignoredVars)
      if (minimalSourceSet.isEmpty() || sourceSet.size < minimalSourceSet.size) {
        minimalSourceSet = sourceSet.toMutableSet()
        finalIgnoredVars = ignoredVars
      }
    }
    finalIgnoredVars.forEach { ignoredVar ->
      if (ignoredVar !in ignoredVarRegistry) {
        ignoredVarRegistry[ignoredVar] = mutableSetOf()
      }
      checkNotNull(ignoredVarRegistry[ignoredVar]).add(state)
    }
    minimalSourceSet.removeAll(exploredActions.toSet())
    return minimalSourceSet
  }

  /**
   * Calculates a source set of enabled actions starting from a set of particular actions.
   *
   * @param enabledActions the enabled actions in the present state
   * @param firstActions the actions that will be added to the source set as the first actions
   * @param prec the precision of the current abstraction
   * @param ignoredVars variables that have been ignored (if they would be in the precision, more
   *   actions have had to be added to the source set)
   * @return a source set of enabled actions in the current abstraction
   */
  private fun calculateSourceSet(
    state: XcfaState<out PtrState<out ExprState>>,
    enabledActions: Collection<XcfaAction>,
    firstActions: Collection<XcfaAction>,
    prec: Prec,
    ignoredVars: MutableSet<VarDecl<*>>,
  ): Set<XcfaAction> {
    if (firstActions.any { it.isBackward }) {
      return enabledActions.toSet()
    }

    val sourceSet = firstActions.toMutableSet()
    val otherActions = enabledActions.toMutableSet() // actions not in the source set
    firstActions.forEach(otherActions::remove)
    val ignoredVarsByAction = otherActions.associateWith { mutableSetOf<VarDecl<*>>() }

    var addedNewAction = true
    while (addedNewAction) {
      addedNewAction = false
      val actionsToRemove = mutableSetOf<XcfaAction>()
      for (action in otherActions) {
        // for every action that is not in the source set it is checked whether it should be added
        // to the source set
        // (because it is dependent with an action already in the source set)
        val potentialIgnoredVars = mutableSetOf<VarDecl<*>>()
        if (sourceSet.any { areDependents(state, it, action, prec, potentialIgnoredVars) }) {
          if (action.isBackward) {
            return enabledActions
              .toSet() // see POR algorithm for the reason of handling backward edges this way
          }
          sourceSet.add(action)
          actionsToRemove.add(action)
          addedNewAction = true
        } else {
          // the action is not added to the source set because we ignore variables in
          // potentialIgnoredVars
          checkNotNull(ignoredVarsByAction[action]).addAll(potentialIgnoredVars)
        }
      }
      actionsToRemove.forEach(otherActions::remove)
    }
    otherActions.forEach { action -> ignoredVars.addAll(checkNotNull(ignoredVarsByAction[action])) }
    return sourceSet
  }

  private fun areDependents(
    state: XcfaState<out PtrState<out ExprState>>,
    sourceSetAction: XcfaAction,
    action: XcfaAction,
    prec: Prec,
    ignoredVariables: MutableSet<VarDecl<*>>,
  ): Boolean {
    if (sourceSetAction.pid == action.pid) return true
    val sourceSetActionVars = getCachedUsedVars(getEdge(sourceSetAction))
    val influencedVars = getInfluencedVars(getEdge(action))
    val sourceSetMemLocs = getCachedMemLocs(getEdge(sourceSetAction))
    val influencedMemLocs = getInfluencedMemLocs(getEdge(action))

    if (
      (influencedMemLocs.filter(MemLoc::isLit) intersect sourceSetMemLocs.filter(MemLoc::isLit))
        .isNotEmpty()
    )
      return true // memlocs aren't necessarily in the prec

    val precVars = prec.usedVars
    for (varDecl in influencedVars) {
      if (varDecl in sourceSetActionVars) {
        if (varDecl !in precVars && varDecl !in fenceVars.values) {
          // the actions would be dependent, but we may have a chance to ignore it in the current
          // abstraction
          ignoredVariables.add(varDecl)
          continue
        }
        return true
      }
    }
    return indirectlyDependent(state, sourceSetAction, sourceSetMemLocs, influencedMemLocs)
  }
}
