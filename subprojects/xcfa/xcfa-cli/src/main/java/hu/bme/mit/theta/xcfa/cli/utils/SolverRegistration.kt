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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.solver.javasmt.JavaSMTSolverManager
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.solver.validator.SolverValidatorWrapperFactory
import hu.bme.mit.theta.solver.z3legacy.Z3SolverManager
import java.nio.file.Path

fun getSolver(name: String, validate: Boolean): SolverFactory =
  if (validate) {
    SolverValidatorWrapperFactory.create(name)
  } else {
    SolverManager.resolveSolverFactory(name)
  }

fun registerAllSolverManagers(home: String, logger: Logger) {
  SolverManager.closeAll()
  // register solver managers
  SolverManager.registerSolverManager(Z3SolverManager.create())
  logger.write(Logger.Level.INFO, "Registered Legacy-Z3 SolverManager\n")
  SolverManager.registerSolverManager(hu.bme.mit.theta.solver.z3.Z3SolverManager.create())
  logger.write(Logger.Level.INFO, "Registered Z3 SolverManager\n")
  SolverManager.registerSolverManager(JavaSMTSolverManager.create())
  logger.write(Logger.Level.INFO, "Registered JavaSMT SolverManager\n")
  val homePath = Path.of(home)
  val smtLibSolverManager: SmtLibSolverManager = SmtLibSolverManager.create(homePath, logger)
  SolverManager.registerSolverManager(smtLibSolverManager)
  logger.write(Logger.Level.INFO, "Registered SMT-LIB SolverManager\n")
}

private var defaultSolversRegistered = false

/**
 * Idempotent convenience wrapper around [registerAllSolverManagers]: registers Theta's built-in
 * solver managers (Z3, JavaSMT, SMT-LIB) exactly once per process, no matter how many times or from
 * how many call sites this is invoked - useful for callers (like `xcfa-dss-analysis`'s tests and
 * `PredicateBlockBehavior`) that need solver names in an
 * [hu.bme.mit.theta.xcfa.cli.params.XcfaConfig] (e.g. `"Z3"`) to resolve through the process-wide
 * [SolverManager] registry, the same way a real `xcfa-cli` invocation's own startup populates it,
 * without needing to reason about whether some other caller already did this first.
 */
@Synchronized
fun ensureDefaultSolversRegistered(
  config: hu.bme.mit.theta.xcfa.cli.params.XcfaConfig<*, *>,
  logger: Logger,
) {
  if (!defaultSolversRegistered) {
    registerAllSolverManagers(config.backendConfig.solverHome, logger)
    defaultSolversRegistered = true
  }
}
