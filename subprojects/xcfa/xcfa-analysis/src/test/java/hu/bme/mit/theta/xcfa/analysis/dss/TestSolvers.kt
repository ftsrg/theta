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
package hu.bme.mit.theta.xcfa.analysis.dss

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.solver.UnknownSolverStatusException
import hu.bme.mit.theta.xcfa.analysis.dss.actor.*
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.registerAllSolverManagers
import java.time.Duration
import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit

/** Time limit of an end-to-end case: the sequential executor analyzes one block at a time. */
val END_TO_END_TIMEOUT: Duration = Duration.ofSeconds(240)

private var defaultSolversRegistered = false

/** Registers Theta's built-in solver managers once per test JVM, as `xcfa-cli`'s startup does. */
@Synchronized
fun ensureDefaultSolversRegistered(config: XcfaConfig<*, *>, logger: Logger) {
  if (!defaultSolversRegistered) {
    registerAllSolverManagers(config.backendConfig.solverHome, logger)
    defaultSolversRegistered = true
  }
}

/**
 * A solver whose [check] returns only when interrupted, as unknown. Never interrupted, it fails
 * with an [AssertionError], which no budget turns into an overrun.
 */
class HangingSolver : Solver {
  private val interrupted = CountDownLatch(1)

  override fun check(): SolverStatus {
    if (!interrupted.await(10, TimeUnit.SECONDS)) throw AssertionError("never interrupted")
    throw UnknownSolverStatusException()
  }

  override fun interrupt() = interrupted.countDown()

  override fun add(assertion: Expr<BoolType>) = Unit

  override fun push() = Unit

  override fun pop(n: Int) = Unit

  override fun reset() = Unit

  override fun getStatus(): SolverStatus = throw UnknownSolverStatusException()

  override fun getModel(): Valuation = error("a hanging solver has no model")

  override fun getAssertions(): Collection<Expr<BoolType>> = emptyList()

  override fun close() = Unit
}

/** Creates [HangingSolver]s only. */
object HangingSolverFactory : SolverFactory {
  override fun createSolver(): Solver = HangingSolver()

  override fun createUCSolver(): UCSolver = error("not needed")

  override fun createItpSolver(): ItpSolver = error("not needed")
}
