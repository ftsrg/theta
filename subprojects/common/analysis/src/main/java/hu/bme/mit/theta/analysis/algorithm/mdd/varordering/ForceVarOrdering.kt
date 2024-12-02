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
package hu.bme.mit.theta.analysis.algorithm.mdd.varordering

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.utils.StmtUtils
import kotlin.random.Random

/**
 * Variable ordering based on the 'FORCE' variable ordering heuristic.
 * https://doi.org/10.1145/764808.764839
 */
fun orderVarsFromRandomStartingPoints(
  vars: List<VarDecl<*>>,
  events: Set<Stmt>,
  numStartingPoints: Int = 5,
): List<VarDecl<*>> {
  val random = Random(0)
  val startingPoints = (0 until numStartingPoints).map { vars.shuffled(random) }
  val orderings = startingPoints.map { orderVars(it, events) }
  return orderings.minBy { eventSpans(it, events) }
}

fun orderVars(vars: List<VarDecl<*>>, events: Set<Stmt>): List<VarDecl<*>> {

  val affectedVars = events.associateWith { event -> StmtUtils.getVars(event) }

  val affectingEvents =
    vars.associateWith { varDecl -> events.filter { varDecl in affectedVars[it]!! }.toSet() }

  var currentVarOrdering = vars.toList()
  var currentEventSpans = eventSpans(currentVarOrdering, events)

  while (true) {
    val cogs =
      events.associateWith {
        affectedVars[it]!!
          .map { varDecl -> currentVarOrdering.indexOf(varDecl) }
          .fold(0, Int::plus)
          .toDouble() / affectedVars[it]!!.size.toDouble()
      }
    val newLocations =
      vars.associateWith { varDecl ->
        affectingEvents[varDecl]!!.map { cogs[it]!! }.fold(0.0, Double::plus) /
          affectingEvents[varDecl]!!.size.toDouble()
      }

    val newVarOrdering = currentVarOrdering.sortedBy { newLocations[it]!! }
    val newEventSpans = eventSpans(newVarOrdering, events)

    if (newEventSpans >= currentEventSpans) {
      break
    } else {
      currentVarOrdering = newVarOrdering
      currentEventSpans = newEventSpans
    }
  }

  return currentVarOrdering
}

private fun eventSpans(vars: List<VarDecl<*>>, events: Set<Stmt>) =
  events
    .map { event ->
      StmtUtils.getVars(event).let {
        when (it.isEmpty()) {
          true -> 0
          else -> {
            val firstVar = it.minOf { vars.indexOf(it) }
            val lastVar = it.maxOf { vars.indexOf(it) }
            lastVar - firstVar
          }
        }
      }
    }
    .fold(0, Int::plus)
