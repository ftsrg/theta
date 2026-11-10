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
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DEFAULT_SEMANTIC_UNROLLINGS
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerCombination
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssGeneralizerKind
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssQuantifiedPredicates
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

/** Which way DSS runs (see `xcfa-analysis's dss/README.md`). */
enum class DssDirection {
  /** From the entry: postconditions forward, violation conditions backward. */
  FORWARD,
  /** DSS on the reversed program, from the error locations towards the entry. */
  BACKWARD,
  /** Both at once, combined where their conditions and summaries meet. */
  BIDIRECTIONAL,
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
  /**
   * The last checker is a finisher: only the blocks whose postconditions no block builds on use it,
   * first (forward the last blocks, backward the first ones); the others go by priority.
   */
  FINISHER,
}

/** The abstract domain of the `CEGAR` entries of [DssConfig.checkerBackends]. */
enum class DssCegarDomain(val domain: Domain) {
  PRED_CART(Domain.PRED_CART),
  /** Tracks the variables of the predicates DSS passes as precision. */
  EXPL(Domain.EXPL),
}

@Serializable
data class DssConfig(
  @Parameter(
    names = ["--dss-decomposition"],
    description = "How to decompose the input procedure into DSS blocks",
  )
  var decomposition: DssDecomposition = DssDecomposition.MERGE,
  @Parameter(
    names = ["--dss-direction"],
    description =
      "FORWARD, BACKWARD (DSS on the reversed program), or BIDIRECTIONAL (both, meeting where " +
        "their conditions intersect)",
  )
  var direction: DssDirection = DssDirection.FORWARD,
  @Parameter(
    names = ["--dss-share-invariants"],
    description =
      "--dss-direction BIDIRECTIONAL: conjoin each direction's converged summaries to the other " +
        "direction's preconditions",
    arity = 1,
  )
  var shareInvariants: Boolean = true,
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
  @Parameter(
    names = ["--dss-cegar-domain"],
    description =
      "Abstract domain of the CEGAR block checkers: PRED_CART, or EXPL tracking the variables of " +
        "the predicates DSS passes as precision",
  )
  var cegarDomain: DssCegarDomain = DssCegarDomain.PRED_CART,
  @Parameter(
    names = ["--dss-interpolate-bounded-proofs"],
    description =
      "Turn the proofs of the BMC/KIND/IMC block checkers into invariants over the program " +
        "variables by interpolation (otherwise path formulas over fresh variables)",
    arity = 1,
  )
  var interpolateBoundedProofs: Boolean = true,
  @Parameter(names = ["--dss-executor"], description = "How the block analyses are run")
  var executor: DssExecutor = DssExecutor.SEQUENTIAL,
  @Parameter(
    names = ["--dss-max-parallel-blocks"],
    description =
      "--dss-executor CONCURRENT: at most this many block analyses run at the same time (0: no " +
        "limit); every block keeps its own thread",
  )
  var maxParallelBlocks: Int = 0,
  @Parameter(
    names = ["--dss-global-predicate-pool"],
    description = "Seed every block's initial precision with every assume condition of the program",
    // Takes a value, so runs that pass `--dss-global-predicate-pool false` keep working
    arity = 1,
  )
  var globalPredicatePool: Boolean = false,
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
  @Parameter(
    names = ["--dss-generalizers"],
    description =
      "Comma-separated generalizers of the received violation conditions (GSPACER, SEMANTIC); " +
        "before each block analysis, their generalization is tried as a probe, never sent or " +
        "reported. None by default",
  )
  var generalizers: List<DssGeneralizerKind> = emptyList(),
  @Parameter(
    names = ["--dss-generalize-violations"],
    description = "The same as adding GSPACER to --dss-generalizers",
  )
  var generalizeViolations: Boolean = false,
  @Parameter(
    names = ["--dss-generalizer-combination"],
    description =
      "How several --dss-generalizers (and --dss-conjecture-generalizers) give one " +
        "generalization: FIRST with a candidate, the UNION of all, or a CHAIN where each weakens " +
        "the previous result",
  )
  var generalizerCombination: DssGeneralizerCombination = DssGeneralizerCombination.FIRST,
  @Parameter(
    names = ["--dss-generalization-gas"],
    description =
      "Failed probes per sender (GSPACER: per sender and condition shape) before it is no " +
        "longer generalized",
  )
  var generalizationGas: Int = 2,
  @Parameter(
    names = ["--dss-semantic-unrollings"],
    description =
      "SEMANTIC probes in a block with an internal cycle: a candidate is checked along the paths " +
        "through at most this many of its back edges (0: no SEMANTIC probes there)",
  )
  var semanticUnrollings: Int = DEFAULT_SEMANTIC_UNROLLINGS,
  @Parameter(
    names = ["--dss-conjecture-invariants"],
    description =
      "Conjecture invariants from violation conditions that keep drifting at a block boundary; " +
        "the blocks check them, and a broken one is retracted (FORWARD or BACKWARD, not PROCESS)",
  )
  var conjectureInvariants: Boolean = false,
  @Parameter(
    names = ["--dss-conjecture-gas"],
    description =
      "--dss-conjecture-invariants: retracted conjectures per location before it gets no more",
  )
  var conjectureGas: Int = 2,
  @Parameter(
    names = ["--dss-block-local-pool"],
    description =
      "Seed a block's initial precision only with the --dss-global-predicate-pool conditions " +
        "over at least one variable of the block",
  )
  var blockLocalPool: Boolean = false,
  @Parameter(
    names = ["--dss-checker-budget"],
    description =
      "Milliseconds a block checker runs before the next one takes its turn; the budget grows " +
        "4-fold after every round of the block checkers (0: a checker runs until it ends). " +
        "Needs --dss-checker-selection PRIORITY",
  )
  var checkerBudgetMs: Long = 0,
  @Parameter(
    names = ["--dss-cut-on-timeout"],
    description =
      "With --dss-checker-budget: a block that every checker runs out of its budget on is cut " +
        "into smaller blocks, and DSS starts over",
  )
  var cutOnTimeout: Boolean = false,
  @Parameter(
    names = ["--dss-solver"],
    description =
      "Solver of the block checkers and of DSS's own queries (default: Z3, or Z3:new for " +
        "--dss-executor CONCURRENT)",
  )
  var solver: String? = null,
  @Parameter(
    names = ["--dss-fallback-solver"],
    description = "A block checker that fails with --dss-solver is retried once with this solver",
  )
  var fallbackSolver: String? = null,
  @Parameter(
    names = ["--dss-quantified-predicates"],
    description =
      "Quantifiers in a block checker's proof (from Z3:new interpolants): KEEP them, retry DSS's " +
        "own failing queries on --dss-fallback-solver (FALLBACK), weaken them away (DROP), or " +
        "eliminate them with Z3 and weaken away the rest (ELIMINATE)",
  )
  var quantifiedPredicates: DssQuantifiedPredicates = DssQuantifiedPredicates.KEEP,
  @Parameter(
    names = ["--dss-expl-checker"],
    description = "Add an EXPL CEGAR block checker after --dss-checker-backends",
  )
  var explChecker: Boolean = false,
  @Parameter(
    names = ["--dss-conjecture-generalizers"],
    description =
      "--dss-conjecture-invariants: comma-separated generalizers that propose the conjectures " +
        "(GSPACER, SEMANTIC), combined by --dss-generalizer-combination",
  )
  var conjectureGeneralizers: List<DssGeneralizerKind> = listOf(DssGeneralizerKind.GSPACER),
  @Parameter(names = ["--dss-worker-port"], hidden = true) var workerPort: Int = 0,
  @Parameter(names = ["--dss-worker-index"], hidden = true) var workerIndex: Int = 0,
  @Parameter(names = ["--dss-worker-blocks"], hidden = true)
  var workerBlocks: List<String> = emptyList(),
  /** The blocks cut so far, in order, so that a worker's block graph is the main process's. */
  @Parameter(names = ["--dss-worker-cuts"], hidden = true)
  var workerCuts: List<String> = emptyList(),
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
