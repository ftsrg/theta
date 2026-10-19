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
import hu.bme.mit.theta.xcfa.dss.actor.DEFAULT_DSS_FALLBACK_SOLVER
import hu.bme.mit.theta.xcfa.dss.actor.DEFAULT_DSS_SOLVER
import kotlinx.serialization.Serializable

/**
 * How DSS cuts the input procedure into blocks (see `dss/DSS.md`). `INLINING` is not implemented.
 */
enum class DssDecomposition {
  /** CPAchecker's `LINEAR_DECOMPOSITION`: a block boundary at every branch/join point/dead end. */
  LINEAR,
  /**
   * CPAchecker's `MERGE_DECOMPOSITION` (its default): `LINEAR`, then horizontal/vertical merging
   * down toward [DssConfig.targetBlockCount].
   */
  MERGE,
  /**
   * Theta-only: `MERGE`, then every self-loop block is absorbed into its neighbouring block, so the
   * loop runs inside one block analysis (`SelfLoopAbsorbingDecomposition`).
   */
  MERGE_ABSORB_SELF_LOOPS,
  /**
   * Theta-only: `MERGE`, then every cycle of the block graph (through any number of blocks) is
   * collapsed into one block, so the block graph is acyclic (`AcyclicMergeDecomposition`).
   */
  MERGE_ACYCLIC,
  /**
   * Theta-only: a cut into [DssConfig.cutBlockCount] blocks with the fewest edges between blocks,
   * then the most equal block sizes (`MinCutDecomposition`); cycles between blocks are allowed.
   */
  MIN_CUT,
  /** `MIN_CUT`, then every self-loop block is collapsed as in `MERGE_ACYCLIC`. */
  MIN_CUT_ABSORB_SELF_LOOPS,
  /** `MIN_CUT` among cuts with an acyclic block graph of at least two blocks only. */
  MIN_CUT_ACYCLIC,
  /** CPAchecker's `NO_DECOMPOSITION`: the whole procedure as a single block. */
  NONE,
}

/**
 * Which DSS executor runs the block graph (see `dss/DSS.md`). Defaults to `SEQUENTIAL`, unlike
 * CPAchecker: legacy Z3 crashes under threads, so `CONCURRENT` needs `--dss-solver Z3:new`.
 */
enum class DssExecutor {
  /** One platform thread per block (`runDssActors`), CPAchecker's `DSS` executor. */
  CONCURRENT,
  /**
   * Deterministic, single-threaded round-robin (`runDssActorsSequentially`), CPAchecker's
   * `SEQUENTIAL`.
   */
  SEQUENTIAL,
  /**
   * Like [CONCURRENT], but every block's analysis runs in a worker process of its own
   * (`runDssActorsInProcesses`), so solvers that are not thread-safe can run in parallel.
   */
  PROCESS,
}

/**
 * Which `DssCheckerSelectionStrategy` picks one of [DssConfig.checkerBackends]' checkers on each
 * recheck (see `dss/DSS.md`). New strategies need a case here plus its translation.
 */
enum class DssCheckerSelectionMethod {
  /** `RoundRobinCheckerSelectionStrategy`: cycles the checker list in order, balanced usage. */
  ROUND_ROBIN,

  /**
   * `PriorityCheckerSelectionStrategy`: always the first checker; the others only as
   * `--dss-checker-fallback` fallbacks, in list order.
   */
  PRIORITY,

  /**
   * `FastestCheckerSelectionStrategy`: a block's first analysis runs every checker, later ones
   * start with the one that finished it fastest, the others following as fallbacks in list order.
   */
  FASTEST,
}

/**
 * Backends a DSS block checker can use: those producing DSS's `LocationInvariants`/`Trace` shape,
 * and only the `PredPrec` CEGAR domains, since others couldn't take the global pool seed.
 */
enum class DssCheckerBackend {
  /** `getCegarChecker` with `Domain.PRED_CART` - DSS's original, only checker. */
  CEGAR_PRED_CART,
  /** `getCegarChecker` with `Domain.PRED_BOOL`. */
  CEGAR_PRED_BOOL,
  /** `getCegarChecker` with `Domain.PRED_SPLIT`. */
  CEGAR_PRED_SPLIT,
  /** `getBoundedChecker`, `--backend BMC`'s own preset: only the SAT-based bounded check. */
  BMC,
  /** `getBoundedChecker`, `--backend KIND`'s own preset: only k-induction. */
  KIND,
  /** `getBoundedChecker`, `--backend IMC`'s own preset: only interpolation-based checking. */
  IMC,
  /** `getBoundedChecker`, `--backend KINDIMC`'s own preset: k-induction and interpolation. */
  KINDIMC,
  /** `getBoundedChecker`, `--backend BOUNDED`'s own preset: every bounded technique enabled. */
  BOUNDED,
}

@Serializable
data class DssConfig(
  @Parameter(
    names = ["--dss-decomposition"],
    description = "How to decompose the input procedure into DSS blocks",
  )
  var decomposition: DssDecomposition = DssDecomposition.MERGE,
  @Parameter(
    names = ["--dss-target-block-count"],
    description =
      "Target block count for --dss-decomposition MERGE(_ABSORB_SELF_LOOPS, _ACYCLIC); ignored otherwise (CPAchecker's " +
        "hardcoded value is 2)",
  )
  var targetBlockCount: Int = 2,
  @Parameter(
    names = ["--dss-largest-horizontal-merge"],
    description =
      "Horizontally merge a group of parallel blocks only if at most one of them has more " +
        "locations than this; -1 disables the limit (CPAchecker's largestHorizontalMerge)",
  )
  var largestHorizontalMerge: Int = -1,
  @Parameter(
    names = ["--dss-allow-single-block-decomposition"],
    description =
      "With --dss-decomposition MERGE(_ABSORB_SELF_LOOPS, _ACYCLIC) and a target of at most one block, use a single block " +
        "(CPAchecker's allowSingleBlockDecompositionWhenMerging)",
  )
  var allowSingleBlockDecomposition: Boolean = false,
  @Parameter(
    names = ["--dss-cut-block-count"],
    description =
      "Number of blocks for --dss-decomposition MIN_CUT(_ABSORB_SELF_LOOPS, _ACYCLIC); fewer if " +
        "no valid cut has that many",
  )
  var cutBlockCount: Int = 2,
  @Parameter(
    names = ["--dss-reset-precision"],
    description =
      "Start every block analysis with the initial precision instead of the precision received " +
        "with the preconditions (CPAchecker's resetPrecisionForEveryRun)",
  )
  var resetPrecisionForEveryRun: Boolean = false,
  @Parameter(
    names = ["--dss-block-graph-stats-only"],
    description =
      "Only decompose the program, log the block graph's statistics (blocks, edges, self loops, " +
        "back-and-forth pairs, cyclic SCCs, ...) and stop with an unknown result (Theta-specific)",
  )
  var blockGraphStatsOnly: Boolean = false,
  @Parameter(
    names = ["--dss-trace"],
    description =
      "Log a DSS-TRACE line at the start and end of every processed message and block analysis " +
        "try (diagnostics, e.g. what a run was doing when it timed out; Theta-specific)",
  )
  var trace: Boolean = false,
  @Parameter(
    names = ["--dss-trace-expressions"],
    description =
      "Implies --dss-trace; the trace lines of sent and received postconditions and violation " +
        "conditions also contain the formula itself (expr=..., last on the line; Theta-specific)",
  )
  var traceExpressions: Boolean = false,
  @Parameter(
    names = ["--dss-reuse-block-precision"],
    description =
      "Start every CEGAR block analysis with the predicates the same block's earlier CEGAR " +
        "analyses ended with, in addition to its usual initial precision (Theta-specific; no " +
        "effect on the bounded checkers of --dss-checker-backends)",
  )
  var reuseBlockPrecision: Boolean = false,
  @Parameter(
    names = ["--dss-checker-fallback"],
    description =
      "If a block analysis's checker throws (solver error, unknown result, unsupported " +
        "operation, ...), repeat it with the next checker of --dss-checker-backends, at most once " +
        "per entry (Theta-specific)",
  )
  var checkerFallback: Boolean = false,
  @Parameter(
    names = ["--dss-solver"],
    description =
      "Solver of the CEGAR block checkers (abstraction and refinement) and of DSS's own coverage " +
        "and satisfiability checks. The default (legacy) Z3 is not safe for --dss-executor " +
        "CONCURRENT; Z3:new is, but its interpolation fails on some C arithmetic - see dss/DSS.md",
  )
  var solver: String = DEFAULT_DSS_SOLVER,
  @Parameter(
    names = ["--dss-solver-fallback"],
    description =
      "If a coverage or satisfiability check of DSS itself fails with --dss-solver (unknown " +
        "result or crash, e.g. Z3 on nonlinear arithmetic), repeat it with " +
        "--dss-fallback-solver. Without this flag, such a failure ends DSS with an unknown " +
        "verdict; with it, only a failure of the fallback solver does - or, where that is " +
        "sound, the check counts as not unsat (Theta-specific)",
  )
  var solverFallback: Boolean = false,
  @Parameter(
    names = ["--dss-checker-solver-fallback"],
    description =
      "If a block checker's check fails (an exception, e.g. Z3's unknown result on nonlinear " +
        "arithmetic or an interpolation it does not support), repeat it with the same checker " +
        "over --dss-fallback-solver (as abstraction, refinement, BMC, induction and " +
        "interpolation solver) before --dss-checker-fallback moves on to the next backend " +
        "(Theta-specific)",
  )
  var checkerSolverFallback: Boolean = false,
  @Parameter(
    names = ["--dss-fallback-solver"],
    description = "Solver of --dss-solver-fallback and --dss-checker-solver-fallback",
  )
  var fallbackSolver: String = DEFAULT_DSS_FALLBACK_SOLVER,
  @Parameter(
    names = ["--dss-executor"],
    description =
      "Which DSS actor-runtime driver to use. SEQUENTIAL by default (CPAchecker's default is " +
        "concurrent): the default solver (Z3) crashes when used by several threads; use " +
        "CONCURRENT together with --dss-solver Z3:new, or PROCESS, which analyzes every block " +
        "in a worker process of its own and so runs any solver in parallel",
  )
  var executor: DssExecutor = DssExecutor.SEQUENTIAL,
  @Parameter(
    names = ["--dss-max-processes"],
    description =
      "--dss-executor PROCESS: at most this many worker processes (0: one per block); a worker " +
        "serving several blocks analyzes them one at a time",
  )
  var maxProcesses: Int = 0,
  @Parameter(
    names = ["--dss-worker-heap"],
    description =
      "--dss-executor PROCESS: maximum heap of each worker process (e.g. 2g); by default the " +
        "workers get the same JVM options as this process",
  )
  var workerHeap: String? = null,
  @Parameter(names = ["--dss-worker-port"], hidden = true) var workerPort: Int = 0,
  @Parameter(names = ["--dss-worker-index"], hidden = true) var workerIndex: Int = 0,
  @Parameter(names = ["--dss-worker-blocks"], hidden = true)
  var workerBlocks: List<String> = emptyList(),
  @Parameter(names = ["--dss-worker-trace-origin"], hidden = true)
  var workerTraceOrigin: Long? = null,
  @Parameter(
    names = ["--dss-global-predicate-pool"],
    description =
      "Seed every block's initial precision with every assume condition of the whole program (default: on). Theta-specific, CPAchecker starts with an empty precision - see dss/DSS.md.",
    // JCommander defaults a Boolean @Parameter to arity 0 (bare presence = true, no way to pass an
    // explicit "false" - fine for every other Boolean flag in this file, which all default false
    // and only ever need turning *on*). This one defaults true and needs to be turned *off* from
    // the CLI, so it needs arity 1 explicitly: `--dss-global-predicate-pool false`.
    arity = 1,
  )
  var globalPredicatePool: Boolean = true,
  @Parameter(
    names = ["--dss-checker-backends"],
    description =
      "Comma-separated list of backends to build DSS's checker-roster factories from; the " +
        "list's length is the roster size (repeat a name for more than one of a kind, e.g. " +
        "CEGAR_PRED_CART,CEGAR_PRED_CART,BMC). CEGAR_PRED_CART/CEGAR_PRED_BOOL/CEGAR_PRED_SPLIT " +
        "are getCegarChecker with the matching Domain, all three still consuming " +
        "--dss-global-predicate-pool's precision seed same as always; the bounded-family entries " +
        "(BMC/KIND/IMC/KINDIMC/BOUNDED) are built via getBoundedChecker with the matching " +
        "--backend preset and do NOT consume that seed (they run on UnitPrec, not XcfaPrec, so " +
        "there is nothing to seed it into). Every block draws its checker for each recheck from " +
        "this same shared roster, chosen by --dss-checker-selection - see dss/DSS.md.",
  )
  var checkerBackends: List<DssCheckerBackend> = listOf(DssCheckerBackend.CEGAR_PRED_CART),
  @Parameter(
    names = ["--dss-checker-selection"],
    description =
      "Policy DssCheckerRoster uses to pick a checker factory on each recheck: ROUND_ROBIN " +
        "cycles the list; PRIORITY always uses the first entry and the others only as " +
        "--dss-checker-fallback fallbacks, in order; FASTEST runs every entry on a block's " +
        "first analysis and from then on starts that block's analyses with the entry that " +
        "finished fastest there, the others following as fallbacks in order (even without " +
        "--dss-checker-fallback)",
  )
  var checkerSelection: DssCheckerSelectionMethod = DssCheckerSelectionMethod.ROUND_ROBIN,
) : SpecBackendConfig

/**
 * A DSS block checker's predicate CEGAR [XcfaConfig] over [domain], all else at defaults. The
 * [cexMonitor] is off by default: its registry is global, so concurrent checkers would mix them up.
 */
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
