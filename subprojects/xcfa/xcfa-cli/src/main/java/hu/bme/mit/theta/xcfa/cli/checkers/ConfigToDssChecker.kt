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
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.dss.actor.CONCURRENT_DSS_SOLVER
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DEFAULT_DSS_SOLVER
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssBlockBehavior
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssBlockWitness
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssConjectureActor
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssCoordinatorFactory
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssExprCodec
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssMeet
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssMeetingActor
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssMeetingSide
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssNetwork
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssResult
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssWorkerLauncher
import hu.bme.mit.theta.xcfa.analysis.dss.actor.PredicateBlockBehavior
import hu.bme.mit.theta.xcfa.analysis.dss.actor.backwardInvariants
import hu.bme.mit.theta.xcfa.analysis.dss.actor.combineInvariants
import hu.bme.mit.theta.xcfa.analysis.dss.actor.fingerprint
import hu.bme.mit.theta.xcfa.analysis.dss.actor.runDssNetworks
import hu.bme.mit.theta.xcfa.analysis.dss.actor.runDssNetworksInProcesses
import hu.bme.mit.theta.xcfa.analysis.dss.actor.runDssNetworksSequentially
import hu.bme.mit.theta.xcfa.analysis.dss.actor.serveDssBlocks
import hu.bme.mit.theta.xcfa.analysis.dss.actor.stitchViolationPath
import hu.bme.mit.theta.xcfa.analysis.dss.actor.violationTrace
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.FastestCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.FinisherCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.ProgramReversal
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.RoundRobinCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.XcfaChecker
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.collectPreds
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.finishingBlocks
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.getPredPrec
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseBlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.reverseProgram
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withSolverConstructionLock
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.AcyclicMergeDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.Block
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.CutLoopHandling
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.DssBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.LinearBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.MergeBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.MinCutDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SelfLoopAbsorbingDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.SingleBlockDecomposition
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.getStatistics
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.XcfaCli
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.CexMonitorOptions
import hu.bme.mit.theta.xcfa.cli.params.DssCegarDomain
import hu.bme.mit.theta.xcfa.cli.params.DssCheckerSelectionMethod
import hu.bme.mit.theta.xcfa.cli.params.DssConfig
import hu.bme.mit.theta.xcfa.cli.params.DssDecomposition
import hu.bme.mit.theta.xcfa.cli.params.DssDirection
import hu.bme.mit.theta.xcfa.cli.params.DssExecutor
import hu.bme.mit.theta.xcfa.cli.params.OutputLevel
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.WitnessLevel
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.params.getDefaultPredCegarConfig
import hu.bme.mit.theta.xcfa.cli.params.toJson
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
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

/** `--backend DSS`: distributed summary synthesis (`xcfa-analysis's dss/README.md`). */
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
          "procedures) - see xcfa-analysis's dss/README.md's Known Limitations."
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
  val direction = dssConfig.direction
  val forwardGraph: BlockGraph? =
    if (direction == DssDirection.BACKWARD) null else decomposition.decompose(procedure)
  val reversal = if (direction == DssDirection.FORWARD) null else reverseProgram(xcfa)
  val backwardGraph: BlockGraph? =
    reversal?.let {
      // Shared block boundaries are where the two directions can meet
      val graph =
        if (forwardGraph != null) reverseBlockGraph(forwardGraph, it)
        else decomposition.decompose(it.procedure)
      graph.checkConsistency()
      graph.withIdPrefix(BACKWARD_BLOCK_PREFIX)
    }
  forwardGraph?.checkConsistency()
  for (graph in listOfNotNull(forwardGraph, backwardGraph)) {
    logger.write(Logger.Level.INFO, "DSS block graph statistics: %s\n", graph.getStatistics())
  }

  require(dssConfig.checkerBackends.isNotEmpty()) {
    "--dss-checker-backends must list at least one backend"
  }
  dssConfig.checkerBackends
    .firstOrNull { it !in DSS_CHECKER_BACKENDS }
    ?.let { throw IllegalArgumentException("--dss-checker-backends: $it cannot check DSS blocks") }
  // Bounded proofs keep path variables whose names recur across runs, so the solver would conflate
  // them when the meeting actor intersects two summaries; a finisher's are kept from it
  val finisherSelection = dssConfig.checkerSelection == DssCheckerSelectionMethod.FINISHER
  val certifiedBackends =
    if (finisherSelection) dssConfig.checkerBackends.dropLast(1) else dssConfig.checkerBackends
  require(
    direction != DssDirection.BIDIRECTIONAL || certifiedBackends.all { it == Backend.CEGAR }
  ) {
    "--dss-direction BIDIRECTIONAL needs CEGAR --dss-checker-backends, except for the finisher " +
      "of FINISHER: the summaries of ${certifiedBackends.filter { it != Backend.CEGAR }} " +
      "cannot be certified"
  }
  val uncertifiedFinisher = finisherSelection && dssConfig.checkerBackends.last() != Backend.CEGAR
  // SAFE under a conjecture needs its coordinator in the quiescence check, and in-process blocks
  require(
    !dssConfig.conjectureInvariants ||
      (direction != DssDirection.BIDIRECTIONAL && dssConfig.executor != DssExecutor.PROCESS)
  ) {
    "--dss-conjecture-invariants needs --dss-direction FORWARD or BACKWARD and a SEQUENTIAL or " +
      "CONCURRENT --dss-executor"
  }
  require(dssConfig.conjectureGas > 0) { "--dss-conjecture-gas must be positive" }
  val blockLogger = BlockAnalysisLogger(logger)
  val solver =
    if (dssConfig.executor == DssExecutor.CONCURRENT) CONCURRENT_DSS_SOLVER else DEFAULT_DSS_SOLVER
  // The counterexample monitor's registry is global: only concurrent block checkers go without it
  val cexMonitor =
    if (dssConfig.executor == DssExecutor.CONCURRENT) CexMonitorOptions.DISABLE
    else CexMonitorOptions.CHECK
  fun checkerFor(backend: Backend): CheckerFactory {
    val blockConfig =
      if (backend == Backend.CEGAR)
        getDefaultPredCegarConfig(dssConfig.cegarDomain.domain, solver, cexMonitor)
      else
        getDefaultConfig(backend).also {
          // Postconditions and witness invariants must be over program variables
          (it.backendConfig.specConfig as BoundedConfig).interpolateProof =
            dssConfig.interpolateBoundedProofs
        }
    return { blockXcfa: XCFA ->
      if (backend == Backend.CEGAR) {
        val cegar = getCegarChecker(blockXcfa, mcm, parseContext, blockConfig, blockLogger)
        if (dssConfig.cegarDomain == DssCegarDomain.EXPL) adaptExplChecker(cegar) else cegar
      } else
        adaptBoundedChecker(getBoundedChecker(blockXcfa, parseContext, blockConfig, blockLogger))
    }
  }
  val checkers: List<CheckerFactory> = dssConfig.checkerBackends.map(::checkerFor)
  val selectionStrategy: DssCheckerSelectionStrategy =
    when (dssConfig.checkerSelection) {
      DssCheckerSelectionMethod.ROUND_ROBIN -> RoundRobinCheckerSelectionStrategy()
      DssCheckerSelectionMethod.PRIORITY -> PriorityCheckerSelectionStrategy()
      DssCheckerSelectionMethod.FASTEST -> FastestCheckerSelectionStrategy()
      DssCheckerSelectionMethod.FINISHER -> {
        require(checkers.size >= 2) {
          "--dss-checker-selection FINISHER: the last --dss-checker-backends entry is the " +
            "finisher, so at least two are needed"
        }
        FinisherCheckerSelectionStrategy()
      }
    }
  val checkerRoster = DssCheckerRoster(checkers, selectionStrategy)
  val dssSolverFactory = SolverManager.resolveSolverFactory(solver)
  val behaviors = ConcurrentHashMap<String, DssBlockBehavior>()
  val bidirectional = direction == DssDirection.BIDIRECTIONAL
  fun behaviorsOf(program: XCFA, programProcedure: XcfaProcedure, finishing: Set<String>) =
    { block: Block ->
      PredicateBlockBehavior(
          program,
          programProcedure,
          block,
          checkerRoster,
          useGlobalPredicatePool = dssConfig.globalPredicatePool,
          resetPrecisionForEveryRun = dssConfig.resetPrecisionForEveryRun,
          reuseBlockPrecision = dssConfig.reuseBlockPrecision,
          checkerFallback = true,
          solverFactory = dssSolverFactory,
          trackSummaries = bidirectional,
          finishing = block.id in finishing,
          generalizationGas = if (dssConfig.generalizeViolations) dssConfig.generalizationGas else 0,
        )
        .also { behaviors[block.id] = it }
    }
  val networks =
    listOfNotNull(
      forwardGraph?.let { DssNetwork(it, behaviorsOf(xcfa, procedure, it.finishingBlocks())) },
      backwardGraph?.let {
        DssNetwork(it, behaviorsOf(reversal!!.xcfa, reversal.procedure, it.finishingBlocks()))
      },
    )
  val forwardIndex = if (forwardGraph != null) 0 else null
  val backwardIndex = if (backwardGraph == null) null else networks.lastIndex
  val forwardCodec by lazy { DssExprCodec(xcfa) }
  val backwardCodec by lazy { DssExprCodec(reversal!!.xcfa) }
  val backwardIds = backwardGraph?.blocks?.mapTo(hashSetOf()) { it.id }.orEmpty()
  val codecOf = { id: String -> if (id in backwardIds) backwardCodec else forwardCodec }

  if (dssConfig.workerPort != 0) {
    val blocks =
      networks
        .flatMap { network -> network.blockGraph.blocks.map { it.id to (it to network) } }
        .toMap()
    serveDssBlocks(
      dssConfig.workerPort,
      dssConfig.workerIndex,
      fingerprint(networks.map { it.blockGraph }),
      dssConfig.workerBlocks.associateWith { id ->
        blocks.getValue(id).let { (block, network) -> network.behaviorFor(block) }
      },
      codecOf,
    )
    kotlin.system.exitProcess(0)
  }

  var meeting: DssMeetingActor? = null
  var conjectures: DssConjectureActor? = null
  val coordinator: DssCoordinatorFactory? =
    if (!bidirectional) {
      if (!dssConfig.conjectureInvariants) null
      else
        { connection ->
          DssConjectureActor(
              connection,
              networks.single().blockGraph,
              dssSolverFactory,
              dssConfig.conjectureGas,
            )
            .also { conjectures = it }
        }
    } else
      { connection ->
        DssMeetingActor(
            connection,
            procedure,
            DssMeetingSide(
              forwardGraph!!,
              procedure.locs.associateWith { it },
              if (uncertifiedFinisher) forwardGraph.finishingBlocks() else emptySet(),
            ),
            DssMeetingSide(
              backwardGraph!!,
              reversal!!.originalOf,
              if (uncertifiedFinisher) backwardGraph.finishingBlocks() else emptySet(),
            ),
            dssSolverFactory,
            sharedVars = procedure.vars + xcfa.globalVars.map { it.wrappedVar },
            shareInvariants = dssConfig.shareInvariants,
          )
          .also { meeting = it }
      }

  val processWitnesses = ConcurrentHashMap<String, DssBlockWitness>()
  val dssRun =
    try {
      when (dssConfig.executor) {
        DssExecutor.CONCURRENT ->
          runDssNetworks(networks, coordinator, maxParallelBlocks = dssConfig.maxParallelBlocks)
        DssExecutor.SEQUENTIAL -> runDssNetworksSequentially(networks, coordinator)
        DssExecutor.PROCESS ->
          runDssNetworksInProcesses(
            networks.map { it.blockGraph },
            getDssWorkerLauncher(config, dssConfig),
            codecOf,
            coordinator,
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
      logBlockStatistics(behaviors.values, logger)
      conjectures?.let {
        logger.write(
          Logger.Level.INFO,
          "DSS conjectures: proposed=%d retracted=%d\n",
          it.proposed,
          it.retracted,
        )
      }
    }

  val witnesses =
    if (dssConfig.executor == DssExecutor.PROCESS) processWitnesses
    else
      behaviors.entries
        .mapNotNull { (id, behavior) ->
          runCatching { behavior.witness() }.getOrNull()?.let { id to it }
        }
        .toMap()
  meeting?.failure?.let {
    logger.write(Logger.Level.INFO, "DSS: the two directions stopped meeting: %s\n", it)
  }
  when (dssRun.result) {
    DssResult.SAFE ->
      SafetyResult.safe(
        when (dssRun.network) {
          forwardIndex -> combineInvariants(procedure, forwardGraph!!, witnesses)
          backwardIndex -> backwardInvariants(reversal!!, backwardGraph!!, witnesses)
          // A cut of disjoint summaries: neither network's invariants are known to hold
          else -> DssInvariants(procedure.locs.associateWith { null })
        }
      )
    DssResult.UNSAFE -> {
      val initial =
        ImmutableValuation.from(
          xcfa.globalVars
            .mapNotNull { global -> global.initValue?.let { global.wrappedVar to it } }
            .toMap()
        )
      val path =
        stitchViolationPath(dssSolverFactory, logger) { solver ->
          when (dssRun.network) {
            forwardIndex -> stitchViolationPath(forwardGraph!!, witnesses, initial, solver)
            // The reversed program starts at the error, in any state
            backwardIndex ->
              stitchViolationPath(backwardGraph!!, witnesses, ImmutableValuation.empty(), solver)
                ?.let(reversal!!::originalPath)
            else ->
              meeting?.meet?.let { meet ->
                meetPath(meet, forwardGraph!!, backwardGraph!!, reversal!!, witnesses, solver)
              }
          }
        }
      val trace = violationTrace(xcfa, procedure.initLoc, path.orEmpty(), initial)
      SafetyResult.unsafe(trace, EmptyProof.getInstance())
    }
  }
}

/** Block ids of the backward network, apart from the forward network's. */
private const val BACKWARD_BLOCK_PREFIX = "R."

/** The block counters summed over every in-process block; worker processes keep their own. */
private fun logBlockStatistics(behaviors: Collection<DssBlockBehavior>, logger: Logger) {
  if (behaviors.isEmpty()) return
  val totals = LinkedHashMap<String, Long>()
  for (behavior in behaviors) {
    for ((name, value) in behavior.statistics()) {
      val number = value.toLongOrNull() ?: continue
      totals.merge(name, number) { a, b -> if (name == "vcMaxAtoms") maxOf(a, b) else a + b }
    }
  }
  if (totals.isEmpty()) return
  logger.write(
    Logger.Level.INFO,
    "DSS block statistics: %s\n",
    totals.entries.joinToString(" ") { "${it.key}=${it.value}" },
  )
}

/** The path to the meeting state from the backward network, then on to the error. */
private fun meetPath(
  meet: DssMeet,
  forwardGraph: BlockGraph,
  backwardGraph: BlockGraph,
  reversal: ProgramReversal,
  witnesses: Map<String, DssBlockWitness>,
  solver: Solver,
): List<XcfaEdge>? {
  fun stitch(graph: BlockGraph, blockId: String, condition: Expr<BoolType>) =
    stitchViolationPath(
      graph,
      witnesses,
      meet.state,
      solver,
      start = graph.blocks.single { it.id == blockId },
      conditions = listOf(condition),
    )
  val toError = stitch(forwardGraph, meet.forwardBlock, meet.forwardCondition) ?: return null
  val fromEntry = stitch(backwardGraph, meet.backwardBlock, meet.backwardCondition) ?: return null
  return reversal.originalPath(fromEntry) + toError
}

private fun stitchViolationPath(
  solverFactory: SolverFactory,
  logger: Logger,
  stitch: (Solver) -> List<XcfaEdge>?,
): List<XcfaEdge>? =
  try {
    withSolverConstructionLock { solverFactory.createSolver() }
      .use(stitch)
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

/** The `--backend`s that check error-location reachability of a single procedure. */
private val DSS_CHECKER_BACKENDS =
  setOf(Backend.CEGAR, Backend.BMC, Backend.KIND, Backend.IMC, Backend.KINDIMC, Backend.BOUNDED)

/** The default [XcfaConfig] of [backend], as `--backend` [backend] would build it. */
private fun getDefaultConfig(backend: Backend): XcfaConfig<*, *> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.backend = backend
  config.backendConfig.createSpecConfig()
  return config
}

/**
 * Runs an EXPL CEGAR checker on DSS's predicate precisions: it tracks the variables of the given
 * predicates, and reports its final precision as one `v = v` atom per tracked variable, the only
 * predicate form that `--dss-reuse-block-precision` can store without changing what it tracks.
 */
fun adaptExplChecker(inner: XcfaChecker): XcfaChecker =
  object : XcfaChecker {
    // The no-argument check lets the checker use its own initial precision; check(null) does not
    override fun check() = reportTrackedVars(inner.check())

    override fun check(input: XcfaPrec<*>?) =
      reportTrackedVars(
        inner.check(
          input?.let {
            XcfaPrec(PtrPrec(ExplPrec.of(ExprUtils.getVars(it.collectPreds())), emptySet()))
          }
        )
      )
  }

private fun reportTrackedVars(
  result: SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>
): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
  val tracked =
    ((result.prec.orElse(null) as? XcfaPrec<*>)?.p as? PtrPrec<*>)?.innerPrec as? ExplPrec
      ?: return result
  val prec = getPredPrec(tracked.vars.map { Eq(it.ref, it.ref) }.toSet())
  val stats = result.stats.orElse(null)
  return when {
    result.isSafe -> SafetyResult.safe(result.proof, stats, prec)
    result.isUnsafe -> SafetyResult.unsafe(result.asUnsafe().cex, result.proof, stats, prec)
    else -> result
  }
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
