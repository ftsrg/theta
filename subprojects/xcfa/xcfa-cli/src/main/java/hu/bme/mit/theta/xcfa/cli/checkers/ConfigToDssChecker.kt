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

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.XcfaCli
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions
import hu.bme.mit.theta.xcfa.cli.params.Domain
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerBackend
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerSelectionMethod
import hu.bme.mit.theta.xcfa.cli.params.DssConfig
import hu.bme.mit.theta.xcfa.cli.params.DssDecomposition
import hu.bme.mit.theta.xcfa.cli.params.DssExecutor
import hu.bme.mit.theta.xcfa.cli.params.OutputLevel
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.WitnessLevel
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.cli.params.toJson
import hu.bme.mit.theta.xcfa.dss.actor.CONCURRENT_DSS_SOLVER
import hu.bme.mit.theta.xcfa.dss.actor.DEFAULT_DSS_SOLVER
import hu.bme.mit.theta.xcfa.dss.actor.DssBlockBehavior
import hu.bme.mit.theta.xcfa.dss.actor.DssBlockWitness
import hu.bme.mit.theta.xcfa.dss.actor.DssExprCodec
import hu.bme.mit.theta.xcfa.dss.actor.DssResult
import hu.bme.mit.theta.xcfa.dss.actor.DssWorkerLauncher
import hu.bme.mit.theta.xcfa.dss.actor.PredicateBlockBehavior
import hu.bme.mit.theta.xcfa.dss.actor.combineInvariants
import hu.bme.mit.theta.xcfa.dss.actor.fingerprint
import hu.bme.mit.theta.xcfa.dss.actor.runDssActors
import hu.bme.mit.theta.xcfa.dss.actor.runDssActorsInProcesses
import hu.bme.mit.theta.xcfa.dss.actor.runDssActorsSequentially
import hu.bme.mit.theta.xcfa.dss.actor.serveDssBlocks
import hu.bme.mit.theta.xcfa.dss.actor.stitchViolationPath
import hu.bme.mit.theta.xcfa.dss.actor.violationTrace
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.dss.analysis.FastestCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.RoundRobinCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.XcfaChecker
import hu.bme.mit.theta.xcfa.dss.analysis.withSolverConstructionLock
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
import hu.bme.mit.theta.xcfa.dss.decomposition.getStatistics
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import java.lang.management.ManagementFactory
import java.nio.file.Files
import java.nio.file.Paths
import java.util.concurrent.ConcurrentHashMap

/**
 * Blocks only search for error locations, so a property must be rewritten to one by a pass first;
 * any other would be reported SAFE unchecked.
 */
fun checkDssSupports(property: XcfaProperty) =
  check(
    property.verifiedProperty == ErrorDetection.ERROR_LOCATION ||
      property.verifiedProperty == ErrorDetection.NO_ASSERTION_VIOLATION
  ) {
    "DSS only checks properties reducible to error-location reachability, not " +
      "${property.verifiedProperty} (input property ${property.inputProperty})"
  }

/** `--backend DSS`: distributed summary synthesis (`dss/DSS.md`). */
fun getDssChecker(
  xcfa: XCFA,
  mcm: MCM,
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  logger: Logger,
): SafetyChecker<Proof, Cex, XcfaPrec<*>> = SafetyChecker { _ ->
  val dssConfig = config.backendConfig.specConfig as DssConfig
  checkDssSupports(config.inputConfig.property)
  val procedure =
    xcfa.procedures.singleOrNull()
      ?: error(
        "DSS only supports single-procedure programs so far (found ${xcfa.procedures.size} " +
          "procedures) - see dss/DSS.md's Known Limitations."
      )

  val decomposition: DssBlockDecomposition =
    when (dssConfig.decomposition) {
      DssDecomposition.LINEAR -> LinearBlockDecomposition()
      DssDecomposition.MERGE -> MergeBlockDecomposition()
      DssDecomposition.MERGE_ABSORB_SELF_LOOPS -> SelfLoopAbsorbingDecomposition()
      DssDecomposition.MERGE_ACYCLIC -> AcyclicMergeDecomposition()
      DssDecomposition.MIN_CUT -> MinCutDecomposition(loopHandling = CutLoopHandling.ALLOW)
      DssDecomposition.MIN_CUT_ABSORB_SELF_LOOPS ->
        MinCutDecomposition(loopHandling = CutLoopHandling.ABSORB_SELF_LOOPS)
      DssDecomposition.MIN_CUT_ACYCLIC -> MinCutDecomposition(loopHandling = CutLoopHandling.FORBID)
      DssDecomposition.NONE -> SingleBlockDecomposition
    }
  val blockGraph: BlockGraph = decomposition.decompose(procedure)
  blockGraph.checkConsistency()
  logger.write(Logger.Level.INFO, "DSS block graph statistics: %s\n", blockGraph.getStatistics())

  require(dssConfig.checkerBackends.isNotEmpty()) {
    "--dss-checker-backends must list at least one backend"
  }
  val blockLogger = BlockAnalysisLogger(logger)
  val solver =
    if (dssConfig.executor == DssExecutor.CONCURRENT) CONCURRENT_DSS_SOLVER else DEFAULT_DSS_SOLVER
  // The counterexample monitor's registry is global: only concurrent block checkers go without it
  val cexMonitor =
    if (dssConfig.executor == DssExecutor.CONCURRENT) CexMonitorOptions.DISABLE
    else CexMonitorOptions.CHECK
  fun checkerFor(backend: DssCheckerBackend): CheckerFactory =
    when (backend) {
      DssCheckerBackend.CEGAR_PRED_CART,
      DssCheckerBackend.CEGAR_PRED_BOOL,
      DssCheckerBackend.CEGAR_PRED_SPLIT -> { blockXcfa: XCFA ->
          getCegarChecker(
            blockXcfa,
            mcm,
            parseContext,
            getDefaultPredCegarConfig(backend.toCegarDomain(), solver, cexMonitor),
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
              getDefaultBoundedConfig(backend.toBoundedBackend()),
              blockLogger,
            )
          )
        }
    }
  val checkers: List<CheckerFactory> = dssConfig.checkerBackends.map(::checkerFor)
  val selectionStrategy: DssCheckerSelectionStrategy =
    when (dssConfig.checkerSelection) {
      DssCheckerSelectionMethod.ROUND_ROBIN -> RoundRobinCheckerSelectionStrategy()
      DssCheckerSelectionMethod.PRIORITY -> PriorityCheckerSelectionStrategy()
      DssCheckerSelectionMethod.FASTEST -> FastestCheckerSelectionStrategy()
    }
  val checkerRoster = DssCheckerRoster(checkers, selectionStrategy)
  val dssSolverFactory = SolverManager.resolveSolverFactory(solver)
  val behaviors = ConcurrentHashMap<String, DssBlockBehavior>()
  val behaviorFor = { block: Block ->
    PredicateBlockBehavior(
        xcfa,
        procedure,
        block,
        checkerRoster,
        useGlobalPredicatePool = dssConfig.globalPredicatePool,
        resetPrecisionForEveryRun = dssConfig.resetPrecisionForEveryRun,
        reuseBlockPrecision = dssConfig.reuseBlockPrecision,
        checkerFallback = true,
        solverFactory = dssSolverFactory,
      )
      .also { behaviors[block.id] = it }
  }

  if (dssConfig.workerPort != 0) {
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

  val processWitnesses = ConcurrentHashMap<String, DssBlockWitness>()
  val dssResult =
    try {
      when (dssConfig.executor) {
        DssExecutor.CONCURRENT -> runDssActors(blockGraph, behaviorFor = behaviorFor)
        DssExecutor.SEQUENTIAL -> runDssActorsSequentially(blockGraph, behaviorFor = behaviorFor)
        DssExecutor.PROCESS ->
          runDssActorsInProcesses(
            blockGraph,
            getDssWorkerLauncher(config, dssConfig),
            DssExprCodec(xcfa),
            witnesses = processWitnesses,
          )
      }
    } catch (e: RuntimeException) {
      val undecided =
        generateSequence<Throwable>(e) { it.cause }.firstOrNull { it is DssUndecidedQueryException }
          ?: throw e
      logger.write(Logger.Level.RESULT, "%s\n", undecided.message)
      return@SafetyChecker SafetyResult.unknown()
    } finally {
      // Block checkers register counterexample monitors globally; later CEGAR runs would see them
      MonitorCheckpoint.reset()
    }

  val witnesses =
    if (dssConfig.executor == DssExecutor.PROCESS) processWitnesses
    else
      behaviors.entries
        .mapNotNull { (id, behavior) ->
          runCatching { behavior.witness() }.getOrNull()?.let { id to it }
        }
        .toMap()
  when (dssResult) {
    DssResult.SAFE -> SafetyResult.safe(combineInvariants(procedure, blockGraph, witnesses))
    DssResult.UNSAFE -> {
      val initial =
        ImmutableValuation.from(
          xcfa.globalVars
            .mapNotNull { global -> global.initValue?.let { global.wrappedVar to it } }
            .toMap()
        )
      val path = stitchViolationPath(blockGraph, witnesses, initial, dssSolverFactory, logger)
      val trace = violationTrace(xcfa, procedure.initLoc, path.orEmpty(), initial)
      SafetyResult.unsafe(trace, EmptyProof.getInstance())
    }
  }
}

private fun stitchViolationPath(
  blockGraph: BlockGraph,
  witnesses: Map<String, DssBlockWitness>,
  initial: ImmutableValuation,
  solverFactory: SolverFactory,
  logger: Logger,
): List<XcfaEdge>? =
  try {
    withSolverConstructionLock { solverFactory.createSolver() }
      .use { solver -> stitchViolationPath(blockGraph, witnesses, initial, solver) }
      .also {
        if (it == null) logger.write(Logger.Level.INFO, "DSS: no violation path to stitch\n")
      }
  } catch (e: Exception) {
    logger.write(Logger.Level.INFO, "DSS: stitching the violation path failed: %s\n", e)
    null
  }

/**
 * Starts DSS worker processes as this JVM with this run's config (`-c`, as `InProcessChecker`), so
 * they decompose the same way.
 */
private fun getDssWorkerLauncher(
  config: XcfaConfig<*, *>,
  dssConfig: DssConfig,
): DssWorkerLauncher {
  @Suppress("UNCHECKED_CAST") val dssRun = config as XcfaConfig<SpecFrontendConfig, DssConfig>
  val java =
    ProcessHandle.current()
      .info()
      .command()
      .orElse(Paths.get(System.getProperty("java.home"), "bin", "java").toString())
  val jvmArgs =
    ManagementFactory.getRuntimeMXBean().inputArguments.filterNot {
      it.startsWith("-agentlib:jdwp")
    }
  return DssWorkerLauncher { index, blockIds, port ->
    val workerConfig =
      dssRun.copy(
        inputConfig = dssRun.inputConfig.copy(xcfaWCtx = null),
        outputConfig =
          dssRun.outputConfig.copy(
            enabled = OutputLevel.NONE,
            witnessConfig = dssRun.outputConfig.witnessConfig.copy(enabled = WitnessLevel.NONE),
          ),
        backendConfig =
          dssRun.backendConfig.copy(
            inProcess = false,
            timeoutMs = 0,
            specConfig =
              dssConfig.copy(workerPort = port, workerIndex = index, workerBlocks = blockIds),
          ),
      )
    val configFile =
      Files.createTempFile("dss-worker-$index-", ".json").toFile().apply {
        deleteOnExit()
        writeText(workerConfig.toJson())
      }
    val command =
      listOf(java) +
        jvmArgs +
        listOf("-cp", System.getProperty("java.class.path"), XcfaCli::class.java.name) +
        listOf("-c", configFile.absolutePath)
    ProcessBuilder(command)
      .redirectOutput(ProcessBuilder.Redirect.DISCARD)
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .start()
  }
}

/** A default [XcfaConfig] for a bounded-model-checking `--backend` preset. */
private fun getDefaultBoundedConfig(backend: Backend): XcfaConfig<*, *> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.backend = backend
  config.backendConfig.createSpecConfig()
  return config
}

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

/** Discards the initial precision; the unchecked cast is safe, as the trace is only read. */
@Suppress("UNCHECKED_CAST")
private fun adaptBoundedChecker(
  inner:
    SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec>
): XcfaChecker = SafetyChecker { _ ->
  inner.check() as SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>
}

/** Demotes block analysis output, so their `SafetyResult` lines aren't taken as the verdict. */
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
