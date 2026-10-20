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

import com.beust.jcommander.Parameter
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.ptr.*
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.por.*
import kotlinx.serialization.Serializable

/** How DSS cuts the input procedure into blocks (see `xcfa-analysis's dss/README.md`). */
enum class DssDecomposition {
  /** CPAchecker's `LINEAR_DECOMPOSITION`: a block boundary at every branch/join point/dead end. */
  LINEAR,
  /** CPAchecker's `MERGE_DECOMPOSITION`: `LINEAR`, then merging down toward two blocks. */
  MERGE,
  /** `MERGE`, then every self-loop block is absorbed into a neighbour. */
  MERGE_ABSORB_SELF_LOOPS,
  /** `MERGE`, then every cycle of the block graph is collapsed into one block. */
  MERGE_ACYCLIC,
  /** A cut into two blocks with the fewest edges between them; cycles between blocks allowed. */
  MIN_CUT,
  /** `MIN_CUT`, then every self-loop block is absorbed into a neighbour. */
  MIN_CUT_ABSORB_SELF_LOOPS,
  /** `MIN_CUT` among cuts with an acyclic block graph only. */
  MIN_CUT_ACYCLIC,
  /** The whole procedure as a single block. */
  NONE,
}

enum class DssExecutor {
  /** One thread per block; uses `Z3:new`, as legacy Z3 is not thread-safe. */
  CONCURRENT,
  /** Deterministic, single-threaded round-robin. */
  SEQUENTIAL,
  /** Every block in a worker process of its own, so any solver can run in parallel. */
  PROCESS,
}

/** How a checker of [DssConfig.checkerBackends] is picked for a block analysis. */
enum class DssCheckerSelectionMethod {
  /** Cycles the checker list. */
  ROUND_ROBIN,
  /** Always the first checker. */
  PRIORITY,
  /** A block's first analysis runs every checker, later ones start with the fastest. */
  FASTEST,
}

@Serializable
data class DssConfig(
  @Parameter(
    names = ["--dss-decomposition"],
    description = "How to decompose the input procedure into DSS blocks",
  )
  var decomposition: DssDecomposition = DssDecomposition.MERGE,
  @Parameter(
    names = ["--dss-checker-backends"],
    description =
      "Comma-separated list of block checker backends (CEGAR, BMC, KIND, IMC, KINDIMC, " +
        "BOUNDED); a failing checker is retried with the next one",
  )
  var checkerBackends: List<Backend> = listOf(Backend.CEGAR),
  @Parameter(
    names = ["--dss-checker-selection"],
    description = "Which of --dss-checker-backends a block analysis starts with",
  )
  var checkerSelection: DssCheckerSelectionMethod = DssCheckerSelectionMethod.PRIORITY,
  @Parameter(names = ["--dss-executor"], description = "How the block analyses are run")
  var executor: DssExecutor = DssExecutor.SEQUENTIAL,
  @Parameter(
    names = ["--dss-global-predicate-pool"],
    description = "Seed every block's initial precision with every assume condition of the program",
    // A Boolean flag that defaults to true needs arity 1 to be turned off
    arity = 1,
  )
  var globalPredicatePool: Boolean = true,
  @Parameter(
    names = ["--dss-reset-precision"],
    description =
      "Start every block analysis with the initial precision instead of the received one",
  )
  var resetPrecisionForEveryRun: Boolean = false,
  @Parameter(
    names = ["--dss-reuse-block-precision"],
    description =
      "Also start every CEGAR block analysis with the predicates of the block's earlier analyses",
  )
  var reuseBlockPrecision: Boolean = false,
  @Parameter(names = ["--dss-worker-port"], hidden = true) var workerPort: Int = 0,
  @Parameter(names = ["--dss-worker-index"], hidden = true) var workerIndex: Int = 0,
  @Parameter(names = ["--dss-worker-blocks"], hidden = true)
  var workerBlocks: List<String> = emptyList(),
) : SpecBackendConfig

/** The cex monitor's registry is global, so concurrent checkers must go without it. */
fun getDefaultPredCegarConfig(
  domain: Domain = Domain.PRED_CART,
  solver: String? = null,
  cexMonitor: CexMonitorOptions = CexMonitorOptions.DISABLE,
): XcfaConfig<SpecFrontendConfig, SpecBackendConfig> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.createSpecConfig()
  val cegarConfig = config.backendConfig.specConfig as CegarConfig
  cegarConfig.abstractorConfig.domain = domain
  cegarConfig.cexMonitor = cexMonitor
  if (solver != null) {
    cegarConfig.abstractorConfig.abstractionSolver = solver
    cegarConfig.refinerConfig.refinementSolver = solver
  }
  return config
}
