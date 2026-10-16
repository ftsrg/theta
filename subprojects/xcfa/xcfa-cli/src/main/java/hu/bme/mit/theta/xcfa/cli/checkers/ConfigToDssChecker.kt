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
package hu.bme.mit.theta.xcfa.cli.checkers

import hu.bme.mit.theta.analysis.EmptyCex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.XcfaCli
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.Domain
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerBackend
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerSelectionMethod
import hu.bme.mit.theta.xcfa.cli.params.DssConfig
import hu.bme.mit.theta.xcfa.cli.params.DssDecomposition
import hu.bme.mit.theta.xcfa.cli.params.DssExecutor
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.params.defaultPredicateCegarConfig
import hu.bme.mit.theta.xcfa.dss.actor.DssExprCodec
import hu.bme.mit.theta.xcfa.dss.actor.DssResult
import hu.bme.mit.theta.xcfa.dss.actor.DssTrace
import hu.bme.mit.theta.xcfa.dss.actor.DssWorkerLauncher
import hu.bme.mit.theta.xcfa.dss.actor.PredicateBlockBehavior
import hu.bme.mit.theta.xcfa.dss.actor.fingerprint
import hu.bme.mit.theta.xcfa.dss.actor.runDssActors
import hu.bme.mit.theta.xcfa.dss.actor.runDssActorsInProcesses
import hu.bme.mit.theta.xcfa.dss.actor.runDssActorsSequentially
import hu.bme.mit.theta.xcfa.dss.actor.serveDssBlocks
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.DssSolverStatistics
import hu.bme.mit.theta.xcfa.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.dss.analysis.FastestCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.RoundRobinCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.XcfaChecker
import hu.bme.mit.theta.xcfa.dss.analysis.withCheckerSolverFallback
import hu.bme.mit.theta.xcfa.dss.decomposition.AcyclicMergeDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.dss.decomposition.CutLoopHandling
import hu.bme.mit.theta.xcfa.dss.decomposition.DssBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.MergeBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.MinCutDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.SelfLoopAbsorbingDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.dss.decomposition.statistics
import hu.bme.mit.theta.xcfa.model.XCFA
import java.lang.management.ManagementFactory
import java.nio.file.Paths
import kotlin.concurrent.thread

/**
 * `--backend DSS`: Distributed Summary Synthesis (`doc/DSS.md`) as a [SafetyChecker], with block
 * checkers from [DssConfig.checkerBackends]. Single-procedure only; yields no cex or proof.
 */
fun getDssChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
): SafetyChecker<EmptyProof, EmptyCex, XcfaPrec<*>> = SafetyChecker { _ ->
  val dssConfig = config.backendConfig.specConfig as DssConfig
  val procedure =
    xcfa.procedures.singleOrNull()
      ?: error(
        "DSS only supports single-procedure programs so far (found ${xcfa.procedures.size} " +
          "procedures) - see doc/DSS.md's Known Limitations."
      )

  // No BlockGraphInstrumentation (CPAchecker's instrumentCFA): every block is extracted into an
  // XCFA with a private exit already, and instrumenting would mutate the input XCFA in place.
  val decomposition: DssBlockDecomposition =
    when (dssConfig.decomposition) {
      DssDecomposition.LINEAR -> LinearBlockDecomposition()
      DssDecomposition.MERGE ->
        MergeBlockDecomposition(
          targetBlockCount = dssConfig.targetBlockCount,
          largestHorizontalMerge = dssConfig.largestHorizontalMerge,
          allowSingleBlockDecomposition = dssConfig.allowSingleBlockDecomposition,
        )
      DssDecomposition.MERGE_ABSORB_SELF_LOOPS ->
        SelfLoopAbsorbingDecomposition(
          targetBlockCount = dssConfig.targetBlockCount,
          largestHorizontalMerge = dssConfig.largestHorizontalMerge,
          allowSingleBlockDecomposition = dssConfig.allowSingleBlockDecomposition,
        )
      DssDecomposition.MERGE_ACYCLIC ->
        AcyclicMergeDecomposition(
          targetBlockCount = dssConfig.targetBlockCount,
          largestHorizontalMerge = dssConfig.largestHorizontalMerge,
          allowSingleBlockDecomposition = dssConfig.allowSingleBlockDecomposition,
        )
      DssDecomposition.MIN_CUT ->
        MinCutDecomposition(dssConfig.cutBlockCount, CutLoopHandling.ALLOW)
      DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS ->
        MinCutDecomposition(dssConfig.cutBlockCount, CutLoopHandling.ABSORB_SELF_LOOPS)
      DssDecomposition.MIN_CUT_ACYCLIC ->
        MinCutDecomposition(dssConfig.cutBlockCount, CutLoopHandling.FORBID)
      DssDecomposition.NONE -> SingleBlockDecomposition
    }
  val statsLevel = if (dssConfig.blockGraphStatsOnly) Logger.Level.RESULT else Logger.Level.INFO
  val blockGraph: BlockGraph =
    if (decomposition is MinCutDecomposition) {
      val cut = decomposition.cut(procedure)
      cut.describe().forEach { logger.write(statsLevel, "%s\n", it) }
      cut.blockGraph
    } else decomposition.decompose(procedure)
  blockGraph.checkConsistency()
  logger.write(statsLevel, "DSS block graph statistics: %s\n", blockGraph.statistics())
  if (dssConfig.blockGraphStatsOnly) return@SafetyChecker SafetyResult.unknown()
  if (dssConfig.trace || dssConfig.traceExpressions) {
    DssTrace.enable(dssConfig.traceExpressions, dssConfig.workerTraceOrigin) {
      logger.write(Logger.Level.RESULT, "%s\n", it)
    }
  }

  require(dssConfig.checkerBackends.isNotEmpty()) {
    "--dss-checker-backends must list at least one backend"
  }
  // One independent factory per dssConfig.checkerBackends entry (distinct instances matter for
  // DssCheckerRoster's index-based bookkeeping); the default list keeps single-checker behavior.
  val blockLogger = BlockAnalysisLogger(logger)
  // solver == null keeps the backend's own default solvers (Z3 for the bounded family)
  fun checkerFor(backend: DssCheckerBackend, solver: String?): CheckerFactory =
    when (backend) {
      DssCheckerBackend.CEGAR_PRED_CART,
      DssCheckerBackend.CEGAR_PRED_BOOL,
      DssCheckerBackend.CEGAR_PRED_SPLIT -> { blockXcfa: XCFA ->
          getCegarChecker(
            blockXcfa,
            mcm,
            parseContext,
            defaultPredicateCegarConfig(backend.toCegarDomain(), solver ?: dssConfig.solver),
            blockLogger,
          )
        }
      DssCheckerBackend.BMC,
      DssCheckerBackend.KIND,
      DssCheckerBackend.IMC,
      DssCheckerBackend.KINDIMC,
      DssCheckerBackend.BOUNDED -> { blockXcfa: XCFA ->
          adaptBoundedChecker(
            getBoundedChecker(
              blockXcfa,
              parseContext,
              defaultBoundedConfigFor(backend.toBoundedBackend(), solver),
              blockLogger,
            )
          )
        }
    }
  val solverStatistics = DssSolverStatistics { stats ->
    logger.write(Logger.Level.RESULT, "DSS solver statistics: %s\n", stats)
  }
  // An unknown fallback solver name fails here, at startup, not at the first failed block check
  if (dssConfig.checkerSolverFallback) SolverManager.resolveSolverFactory(dssConfig.fallbackSolver)
  val checkers: List<CheckerFactory> =
    dssConfig.checkerBackends.map { backend ->
      if (dssConfig.checkerSolverFallback)
        withCheckerSolverFallback(
          checkerFor(backend, null),
          checkerFor(backend, dssConfig.fallbackSolver),
          solverStatistics,
        )
      else checkerFor(backend, null)
    }
  val selectionStrategy: DssCheckerSelectionStrategy =
    when (dssConfig.checkerSelection) {
      DssCheckerSelectionMethod.ROUND_ROBIN -> RoundRobinCheckerSelectionStrategy()
      DssCheckerSelectionMethod.PRIORITY -> PriorityCheckerSelectionStrategy()
      DssCheckerSelectionMethod.FASTEST -> FastestCheckerSelectionStrategy()
    }
  // Built once, not in behaviorFor: DssCheckerRoster requires one instance shared by all blocks.
  val checkerRoster = DssCheckerRoster(checkers, selectionStrategy)
  val dssSolverFactory = SolverManager.resolveSolverFactory(dssConfig.solver)
  val dssFallbackSolverFactory =
    if (dssConfig.solverFallback) SolverManager.resolveSolverFactory(dssConfig.fallbackSolver)
    else null
  val behaviorFor = { block: Block ->
    PredicateBlockBehavior(
      xcfa,
      procedure,
      block,
      checkerRoster,
      useGlobalPredicatePool = dssConfig.globalPredicatePool,
      resetPrecisionForEveryRun = dssConfig.resetPrecisionForEveryRun,
      reuseBlockPrecision = dssConfig.reuseBlockPrecision,
      checkerFallback = dssConfig.checkerFallback,
      solverFactory = dssSolverFactory,
      fallbackSolverFactory = dssFallbackSolverFactory,
      solverStatistics = solverStatistics,
    )
  }

  if (dssConfig.workerPort != 0) {
    // A worker process of --dss-executor PROCESS: answers for its blocks, never reports a verdict
    val blocks = blockGraph.blocks.associateBy { it.id }
    serveDssBlocks(
      dssConfig.workerPort,
      dssConfig.workerIndex,
      blockGraph.fingerprint(),
      dssConfig.workerBlocks.associateWith { behaviorFor(blocks.getValue(it)) },
      DssExprCodec(xcfa),
    )
    kotlin.system.exitProcess(0)
  }

  val dssResult =
    try {
      when (dssConfig.executor) {
        DssExecutor.CONCURRENT -> runDssActors(blockGraph, behaviorFor = behaviorFor)
        DssExecutor.SEQUENTIAL -> runDssActorsSequentially(blockGraph, behaviorFor = behaviorFor)
        DssExecutor.PROCESS ->
          runDssActorsInProcesses(
            blockGraph,
            dssWorkerLauncher(dssConfig),
            DssExprCodec(xcfa),
            dssConfig.maxProcesses,
          )
      }
    } catch (e: RuntimeException) {
      // Usually wrapped: the observer rethrows a block's failure, see DssObserverActor.verdict
      val undecided =
        generateSequence<Throwable>(e) { it.cause }.firstOrNull { it is DssUndecidedQueryException }
          ?: throw e
      logger.write(Logger.Level.RESULT, "%s\n", undecided.message)
      return@SafetyChecker SafetyResult.unknown()
    } finally {
      DssTrace.disable()
      logger.write(Logger.Level.RESULT, "DSS solver statistics: %s\n", solverStatistics)
    }

  when (dssResult) {
    DssResult.SAFE -> SafetyResult.safe(EmptyProof.getInstance())
    DssResult.UNSAFE -> SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
  }
}

/**
 * Starts DSS worker processes as this JVM with the command line of this run, so that each parses
 * the program and decomposes it the same way. Workers write no output files; their trace lines are
 * copied to this process's output, everything else they print is dropped.
 */
private fun dssWorkerLauncher(dssConfig: DssConfig): DssWorkerLauncher {
  val args =
    XcfaCli.launchArgs ?: error("--dss-executor PROCESS needs xcfa-cli's own main (XcfaCli.main)")
  val java =
    ProcessHandle.current()
      .info()
      .command()
      .orElse(Paths.get(System.getProperty("java.home"), "bin", "java").toString())
  val heap = dssConfig.workerHeap
  val jvmArgs =
    ManagementFactory.getRuntimeMXBean().inputArguments.filterNot {
      it.startsWith("-agentlib:jdwp") || (heap != null && it.startsWith("-Xmx"))
    } + listOfNotNull(heap?.let { "-Xmx$it" })
  val traceOrigin = if (DssTrace.enabled) DssTrace.originEpochMillis() else null
  return DssWorkerLauncher { index, blockIds, port ->
    val command =
      listOf(java) +
        jvmArgs +
        listOf("-cp", System.getProperty("java.class.path"), XcfaCli::class.java.name) +
        args +
        listOf("--output", "NONE", "--witness-generation", "NONE") +
        listOf("--dss-worker-port", "$port", "--dss-worker-index", "$index") +
        listOf("--dss-worker-blocks", blockIds.joinToString(",")) +
        (traceOrigin?.let { listOf("--dss-worker-trace-origin", "$it") } ?: emptyList())
    val process = ProcessBuilder(command).redirectError(ProcessBuilder.Redirect.INHERIT).start()
    thread(isDaemon = true, name = "dss-worker-$index-output") {
      process.inputStream.bufferedReader().forEachLine {
        if (it.startsWith("DSS-TRACE ")) println(it)
      }
    }
    process
  }
}

/**
 * A default [XcfaConfig] for a bounded-model-checking `--backend` preset, via
 * `BackendConfig.createSpecConfig` so it can't drift from the flag. [solver] replaces its solvers.
 */
private fun defaultBoundedConfigFor(backend: Backend, solver: String? = null): XcfaConfig<*, *> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.backend = backend
  config.backendConfig.createSpecConfig()
  if (solver != null) {
    val bounded = config.backendConfig.specConfig as BoundedConfig
    bounded.bmcConfig.bmcSolver = solver
    bounded.indConfig.indSolver = solver
    bounded.itpConfig.itpSolver = solver
  }
  return config
}

/** Maps a bounded-family [DssCheckerBackend] to its [Backend]; `CEGAR_*` entries never get here. */
private fun DssCheckerBackend.toBoundedBackend(): Backend =
  when (this) {
    DssCheckerBackend.BMC -> Backend.BMC
    DssCheckerBackend.KIND -> Backend.KIND
    DssCheckerBackend.IMC -> Backend.IMC
    DssCheckerBackend.KINDIMC -> Backend.KINDIMC
    DssCheckerBackend.BOUNDED -> Backend.BOUNDED
    DssCheckerBackend.CEGAR_PRED_CART,
    DssCheckerBackend.CEGAR_PRED_BOOL,
    DssCheckerBackend.CEGAR_PRED_SPLIT ->
      throw IllegalArgumentException("$this has no bounded-family Backend")
  }

/** Maps a `CEGAR_*` [DssCheckerBackend] to its [Domain]; bounded entries never get here. */
private fun DssCheckerBackend.toCegarDomain(): Domain =
  when (this) {
    DssCheckerBackend.CEGAR_PRED_CART -> Domain.PRED_CART
    DssCheckerBackend.CEGAR_PRED_BOOL -> Domain.PRED_BOOL
    DssCheckerBackend.CEGAR_PRED_SPLIT -> Domain.PRED_SPLIT
    DssCheckerBackend.BMC,
    DssCheckerBackend.KIND,
    DssCheckerBackend.IMC,
    DssCheckerBackend.KINDIMC,
    DssCheckerBackend.BOUNDED ->
      throw IllegalArgumentException("$this is not a CEGAR entry, has no Domain")
  }

/**
 * Adapts a [UnitPrec] bounded checker to the roster's [XcfaChecker] shape, discarding the initial
 * [XcfaPrec] (the global pool seed). The cast is unchecked but safe: the trace is only read.
 */
@Suppress("UNCHECKED_CAST")
private fun adaptBoundedChecker(
  inner:
    SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec>
): XcfaChecker = SafetyChecker { _ ->
  inner.check() as SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>
}

/**
 * Logger for block analyses: demotes messages to at least [Logger.Level.DETAIL], so per-block
 * `SafetyResult` lines can't be mistaken for DSS's verdict (e.g. by BenchExec's tool-info).
 */
private class BlockAnalysisLogger(private val delegate: Logger) : Logger {
  override fun write(level: Logger.Level, pattern: String, vararg objects: Any?): Logger {
    val demoted =
      when {
        level == Logger.Level.DISABLE -> level
        level <= Logger.Level.SUBSTEP -> Logger.Level.DETAIL
        else -> Logger.Level.VERBOSE
      }
    delegate.write(demoted, pattern, *objects)
    return this
  }
}
