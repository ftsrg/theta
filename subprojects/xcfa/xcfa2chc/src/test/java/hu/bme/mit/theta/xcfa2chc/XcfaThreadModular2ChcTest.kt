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
package hu.bme.mit.theta.xcfa2chc

import hu.bme.mit.theta.common.OsHelper
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.smtlib.testing.SolverInstallations
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.global
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

class XcfaThreadModular2ChcTest {

  companion object {
    private lateinit var solverFactory: SolverFactory

    @BeforeAll
    @JvmStatic
    fun init() {
      Assumptions.assumeTrue(OsHelper.getOs() == OsHelper.OperatingSystem.LINUX)
      solverFactory = SolverInstallations.installOrSkip("z3", "4.13.0")
    }
  }

  private fun check(xcfa: XCFA): SolverStatus {
    val solver = solverFactory.createHornSolver()
    solver.add(xcfa.toThreadModularCHC())
    solver.check()
    return solver.status
  }

  /** Main starts any number of threads (in a loop); each increments `x` atomically. */
  private fun counter(threadBody: Boolean): XCFA =
    xcfa("counter") {
      global { "x" type Int() init "0" }
      val thr =
        procedure("thr") {
          (init to "L") {
            atomic_begin()
            "x" assign "(+ x 1)"
            atomic_end()
          }
          if (threadBody) (("L" to err) { assume("(< x 0)") })
          else (("L" to err) { assume("(= x 3)") })
          ("L" to final) { nop() }
        }
      val main =
        procedure("main") {
          "t" type Int()
          (init to "L") { "x" assign "0" }
          ("L" to "L") { "t".start(thr) }
          ("L" to err) { assume("(< x 0)") }
          ("L" to final) { nop() }
        }
      main.start()
    }

  @Test
  fun unboundedThreadsSafe() {
    assertEquals(SolverStatus.SAT, check(counter(threadBody = true)))
  }

  @Test
  fun unboundedThreadsReachable() {
    // Three threads reach x == 3, so the system has no model.
    assertEquals(SolverStatus.UNSAT, check(counter(threadBody = false)))
  }

  @Test
  fun noInterferenceInsideAtomicBlock() {
    val xcfa =
      xcfa("atomic") {
        global { "x" type Int() init "0" }
        val thr =
          procedure("thr") {
            (init to "A") {
              atomic_begin()
              "x" assign "1"
            }
            ("A" to err) { assume("(/= x 1)") }
            ("A" to final) { atomic_end() }
          }
        val main =
          procedure("main") {
            "t" type Int()
            (init to "L") { "x" assign "0" }
            ("L" to "L") { "t".start(thr) }
            ("L" to "L") { "x" assign "0" }
            ("L" to final) { nop() }
          }
        main.start()
      }
    assertEquals(SolverStatus.SAT, check(xcfa))
  }

  @Test
  fun interferenceOutsideAtomicBlock() {
    val xcfa =
      xcfa("nonatomic") {
        global { "x" type Int() init "0" }
        val thr =
          procedure("thr") {
            (init to "A") { "x" assign "1" }
            ("A" to err) { assume("(/= x 1)") }
            ("A" to final) { nop() }
          }
        val main =
          procedure("main") {
            "t" type Int()
            (init to "L") { "x" assign "0" }
            ("L" to "L") { "t".start(thr) }
            ("L" to "L") { "x" assign "0" }
            ("L" to final) { nop() }
          }
        main.start()
      }
    assertEquals(SolverStatus.UNSAT, check(xcfa))
  }

  @Test
  fun startArgumentBindsParameter() {
    val xcfa =
      xcfa("args") {
        val thr =
          procedure("thr") {
            ("ret" type Int()).direction(hu.bme.mit.theta.xcfa.model.ParamDirection.OUT)
            ("p" type Int()).direction(hu.bme.mit.theta.xcfa.model.ParamDirection.IN)
            (init to err) { assume("(/= p 5)") }
            (init to final) { nop() }
          }
        val main =
          procedure("main") {
            "t" type Int()
            "a" type Int()
            (init to "L") { "a" assign "5" }
            ("L" to "L") { "t".start(thr, "0", "a") }
            ("L" to final) { nop() }
          }
        main.start()
      }
    assertEquals(SolverStatus.SAT, check(xcfa))
  }

  @Test
  fun mutexIsRejected() {
    val xcfa =
      xcfa("mutex") {
        global { "x" type Int() init "0" }
        val main =
          procedure("main") {
            (init to final) {
              mutex_lock("x")
              mutex_unlock("x")
            }
          }
        main.start()
      }
    assertThrows<IllegalStateException> { xcfa.toThreadModularCHC() }
  }
}
