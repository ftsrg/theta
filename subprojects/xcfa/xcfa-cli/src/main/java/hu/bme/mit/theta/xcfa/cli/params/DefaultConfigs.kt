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
package hu.bme.mit.theta.xcfa.cli.params

/**
 * Builds a predicate-abstraction CEGAR [XcfaConfig] over [domain], all else at defaults, for
 * callers building a config by hand rather than loading one from a file (e.g. DSS).
 */
fun defaultPredicateCegarConfig(
  domain: Domain = Domain.PRED_CART,
  solver: String? = null,
): XcfaConfig<SpecFrontendConfig, SpecBackendConfig> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.createSpecConfig()
  val cegarConfig = config.backendConfig.specConfig as CegarConfig
  cegarConfig.abstractorConfig.domain = domain
  if (solver != null) {
    cegarConfig.abstractorConfig.abstractionSolver = solver
    cegarConfig.refinerConfig.refinementSolver = solver
  }
  return config
}
