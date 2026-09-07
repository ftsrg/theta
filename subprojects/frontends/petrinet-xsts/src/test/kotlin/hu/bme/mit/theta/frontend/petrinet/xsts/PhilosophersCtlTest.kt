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
package hu.bme.mit.theta.frontend.petrinet.xsts

import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.MddCtlChecker
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.ctl.CtlParser
import hu.bme.mit.theta.frontend.petrinet.pnml.XMLPnmlToPetrinet
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import hu.bme.mit.theta.xsts.analysis.XstsToMonolithicAdapter
import java.io.ByteArrayInputStream
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Symbolic CTL model checking of the 5-philosopher dining net. The eating places are Eat_1 ..
 * Eat_5; philosopher i shares a fork with philosophers i-1 and i+1 (wrap-around). This net has no
 * deadlock-avoidance, so it can deadlock.
 */
class PhilosophersCtlTest {

  private fun check(property: String): Boolean {
    val petriNet = XMLPnmlToPetrinet.parse("src/test/resources/pnml/Philosophers-5.pnml", "")
    val xsts =
      ByteArrayInputStream("prop { true }".toByteArray()).use {
        PetriNetToXSTS.createXSTS(petriNet, it)
      }
    val monolithicExpr = XstsToMonolithicAdapter(xsts).monolithicExpr
    return SolverPool(Z3LegacySolverFactory.getInstance()).use { pool ->
      val checker = MddCtlChecker(monolithicExpr, pool, NullLogger.getInstance())
      checker.isSatisfied(CtlParser.parse(property, monolithicExpr.vars))
    }
  }

  @Test
  fun eachPhilosopherCanEat() {
    for (i in 1..5) assertTrue(check("EF(Eat_$i > 0)"), "philosopher $i should be able to eat")
  }

  @Test
  fun nonAdjacentPhilosophersCanEatConcurrently() {
    // 1 and 3 share no fork, so they can hold all four needed forks at once
    assertTrue(check("EF(Eat_1 > 0 & Eat_3 > 0)"))
  }

  @Test
  fun adjacentPhilosophersNeverEatConcurrently() {
    // shared fork enforces mutual exclusion between neighbours
    assertTrue(check("AG(!(Eat_1 > 0 & Eat_2 > 0))"))
    assertTrue(check("AG(!(Eat_5 > 0 & Eat_1 > 0))"))
  }

  @Test
  fun netCanDeadlock() {
    // AG EX true asserts every reachable state has a successor; it fails because all five can grab
    // their left fork and block
    assertFalse(check("AG(EX(true))"))
  }

  @Test
  fun aPhilosopherCanStarve() {
    // from the deadlock state eating is no longer reachable, so the recurrence property fails
    assertFalse(check("AG(EF(Eat_1 > 0))"))
  }

  @Test
  fun universalLivenessFails() {
    assertFalse(
      check("AG(EF(Eat_1 > 0) & EF(Eat_2 > 0) & EF(Eat_3 > 0) & EF(Eat_4 > 0) & EF(Eat_5 > 0))")
    )
  }
}
