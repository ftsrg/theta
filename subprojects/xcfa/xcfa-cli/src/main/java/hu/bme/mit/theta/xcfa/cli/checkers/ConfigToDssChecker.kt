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
import hu.bme.mit.theta.xcfa.cli.params.Backend
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
import hu.bme.mit.theta.xcfa.dss.actor.DssResult
import hu.bme.mit.theta.xcfa.dss.actor.DssTrace
import hu.bme.mit.theta.xcfa.dss.actor.PredicateBlockBehavior
import hu.bme.mit.theta.xcfa.dss.actor.runDssActors
import hu.bme.mit.theta.xcfa.dss.actor.runDssActorsSequentially
import hu.bme.mit.theta.xcfa.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerRoster
import hu.bme.mit.theta.xcfa.dss.analysis.DssCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.PriorityCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.RoundRobinCheckerSelectionStrategy
import hu.bme.mit.theta.xcfa.dss.analysis.XcfaChecker
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

/**
 * `--backend DSS`: runs Distributed Summary Synthesis instead of an ordinary, monolithic checker -
 * see `doc/DSS.md` for the full design. Wrapped as an ordinary [SafetyChecker] lambda (mirroring
 * `getPortfolioChecker`, the closest existing precedent for "the algorithm isn't a single
 * `SafetyChecker.check()` call") so it flows through exactly the same result-reporting/witness
 * pipeline every other backend already uses (`ExecuteConfig.kt`'s `backend()`).
 *
 * DSS only supports a single procedure so far (`doc/DSS.md`'s Known Limitations - block
 * decomposition happens per-procedure, not yet across procedure boundaries); a multi-procedure
 * input fails fast with a clear message rather than silently checking only one procedure.
 *
 * [DssConfig.checkerBackends] lists which backend builds each of [DssCheckerRoster]'s checker
 * factories, one entry per roster slot (repeat a name for more than one of a kind) -
 * `--dss-checker-backends CEGAR_PRED_CART` (the default, a one-element list) reproduces the
 * original byte-for-byte single-checker behavior. The three `CEGAR_*` entries
 * ([DssCheckerBackend.CEGAR_PRED_CART]/[CEGAR_PRED_BOOL][DssCheckerBackend.CEGAR_PRED_BOOL]/
 * [CEGAR_PRED_SPLIT][DssCheckerBackend.CEGAR_PRED_SPLIT]) are all [getCegarChecker] with
 * [defaultPredicateCegarConfig] - the same "thin orchestration layer" every DSS test in
 * `xcfa-dss-actor` builds by hand, just assembled here instead - differing only in which [Domain]
 * gets passed through; all three still consume `--dss-global-predicate-pool`'s seed exactly like
 * the original, sole `CEGAR` option always did (see [DssCheckerBackend]'s own doc for why only
 * these three, not [Domain.EXPL]/the product domains). The bounded-model-checking family
 * (`BMC`/`KIND`/`IMC`/`KINDIMC`/`BOUNDED` - see [DssCheckerBackend]'s own doc) is built via
 * [getBoundedChecker] with the matching `--backend` preset ([defaultBoundedConfigFor] reuses
 * `BackendConfig.createSpecConfig`'s own dispatch, so it can't drift from what that flag actually
 * means) and [adaptBoundedChecker]ed into the roster's own [XcfaChecker] shape - see that
 * function's own doc for why the adaptation silently drops `--dss-global-predicate-pool`'s
 * precision seed for those entries specifically (they run on [UnitPrec], not [XcfaPrec], so there
 * is nothing to seed it into). There is currently no `--dss-worker-config` flag to substitute a
 * genuinely *different* worker configuration beyond the domain/backend choice itself (e.g. a
 * non-default solver or search strategy) - see the plan's open questions on why this is more
 * involved than it first looks. [DssConfig.checkerSelection] picks which
 * [DssCheckerSelectionStrategy] the roster uses to choose among its factories on each recheck
 * (`ROUND_ROBIN` today, matching [DssCheckerRoster]'s own default). `--dss-global-predicate-pool`
 * (default on) is otherwise pass-through to every block's own [PredicateBlockBehavior] - see that
 * class's own doc for what turning it off actually changes.
 *
 * DSS produces no concrete counterexample trace ([EmptyCex]) and no invariant proof beyond a
 * trivial one ([EmptyProof]) for either verdict - matching the paper's own stated "Verification
 * Witnesses" limitation (DSS cannot yet produce violation witnesses), and CPAchecker's own
 * implementation, which does not restore one either; it just flips the verdict.
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

  // CPAchecker instruments every block end with a ghost edge to a dedicated violation-condition
  // location after decomposing (BlockGraphModification.instrumentCFA, on a copy of the CFA). Not
  // needed here: every block is extracted into its own XCFA, where the block exit is a private
  // location already (see extractBlockXcfa), and BlockGraphInstrumentation would mutate the input
  // XCFA's locations in place.
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
  if (dssConfig.trace) DssTrace.enable { logger.write(Logger.Level.RESULT, "%s\n", it) }

  require(dssConfig.checkerBackends.isNotEmpty()) {
    "--dss-checker-backends must list at least one backend"
  }
  // One independent factory per dssConfig.checkerBackends entry - .map already calls its lambda
  // fresh for every element, so the roster holds distinct instances (matters for DssCheckerRoster's
  // index-based bookkeeping, not just its size), not shared references to one closure.
  // --dss-checker-backends CEGAR_PRED_CART (the default, a one-element list) is therefore still
  // byte-for-byte the original single-checker behavior.
  val blockLogger = BlockAnalysisLogger(logger)
  val checkers: List<CheckerFactory> =
    dssConfig.checkerBackends.map { backend ->
      when (backend) {
        DssCheckerBackend.CEGAR_PRED_CART,
        DssCheckerBackend.CEGAR_PRED_BOOL,
        DssCheckerBackend.CEGAR_PRED_SPLIT -> { blockXcfa: XCFA ->
            getCegarChecker(
              blockXcfa,
              mcm,
              parseContext,
              defaultPredicateCegarConfig(backend.toCegarDomain(), dssConfig.solver),
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
                defaultBoundedConfigFor(backend.toBoundedBackend()),
                blockLogger,
              )
            )
          }
      }
    }
  val selectionStrategy: DssCheckerSelectionStrategy =
    when (dssConfig.checkerSelection) {
      DssCheckerSelectionMethod.ROUND_ROBIN -> RoundRobinCheckerSelectionStrategy()
      DssCheckerSelectionMethod.PRIORITY -> PriorityCheckerSelectionStrategy()
    }
  // Built once, here - not inside behaviorFor - so it's the one shared instance every block's
  // PredicateBlockBehavior gets, per DssCheckerRoster's own contract (a fresh roster per block
  // would
  // silently give each block its own independent selection-strategy state instead of one shared
  // across the whole run).
  val checkerRoster = DssCheckerRoster(checkers, selectionStrategy)
  val dssSolverFactory = SolverManager.resolveSolverFactory(dssConfig.solver)
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
    )
  }

  val dssResult =
    try {
      when (dssConfig.executor) {
        DssExecutor.CONCURRENT -> runDssActors(blockGraph, behaviorFor = behaviorFor)
        DssExecutor.SEQUENTIAL -> runDssActorsSequentially(blockGraph, behaviorFor = behaviorFor)
      }
    } finally {
      DssTrace.disable()
    }

  when (dssResult) {
    DssResult.SAFE -> SafetyResult.safe(EmptyProof.getInstance())
    DssResult.UNSAFE -> SafetyResult.unsafe(EmptyCex.getInstance(), EmptyProof.getInstance())
  }
}

/**
 * Builds a default [XcfaConfig] for one of the bounded-model-checking family's `--backend` presets
 * ([Backend.BMC]/[Backend.KIND]/[Backend.IMC]/[Backend.KINDIMC]/[Backend.BOUNDED]) - reuses
 * `BackendConfig.createSpecConfig`'s own dispatch, the exact same switch a real `--backend BMC`
 * (etc.) invocation goes through, so this can never drift from what that flag actually means. Not
 * meant for [Backend.CEGAR] - see [defaultPredicateCegarConfig] for that one instead.
 */
private fun defaultBoundedConfigFor(backend: Backend): XcfaConfig<*, *> {
  val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
  config.backendConfig.backend = backend
  config.backendConfig.createSpecConfig()
  return config
}

/**
 * [DssCheckerBackend]'s own bounded-model-checking-family entries, mapped onto the real [Backend]
 * value [defaultBoundedConfigFor]/[getBoundedChecker] need - the three `CEGAR_*` entries have no
 * bounded-family shape and are handled separately in [getDssChecker] (see [toCegarDomain]), never
 * routed through here.
 */
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

/**
 * [DssCheckerBackend]'s own three CEGAR entries, mapped onto the [Domain]
 * [defaultPredicateCegarConfig] needs - the bounded-model-checking-family entries have no [Domain]
 * (they aren't CEGAR at all) and are handled separately in [getDssChecker] (see
 * [toBoundedBackend]), never routed through here.
 */
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
 * Adapts a [UnitPrec]-based checker ([getBoundedChecker]'s own return shape - the bounded-model-
 * checking family's own precision type, unrelated to [XcfaPrec]) into the roster's own
 * [XcfaChecker] shape. The incoming [XcfaPrec] initial precision (DSS's
 * `--dss-global-predicate-pool` seed, when [PredicateBlockBehavior] passes one) is discarded, not
 * translated - [UnitPrec] carries no information to translate it *into*, so a bounded-family roster
 * entry always runs exactly as its own [defaultBoundedConfigFor] preset would standalone, silently
 * skipping that seed (see [DssConfig.checkerBackends]'s own doc).
 *
 * The cast below is unchecked but safe: generics are erased at runtime, so a real
 * `Trace<XcfaState<PtrState<ExplState>>, XcfaAction>` value already *is* a valid value to read as
 * `Trace<XcfaState<PtrState<*>>, XcfaAction>` - nothing here writes into it under the assumed type,
 * only re-exposes what [getBoundedChecker] already produced under a wider read-only view.
 */
@Suppress("UNCHECKED_CAST")
private fun adaptBoundedChecker(
  inner:
    SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<ExplState>>, XcfaAction>, UnitPrec>
): XcfaChecker = SafetyChecker { _ ->
  inner.check() as SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>>
}

/**
 * The logger of the block analyses: forwards to [delegate] with every message demoted to at least
 * [Logger.Level.DETAIL] (finer messages to [Logger.Level.VERBOSE]). Every block analysis is an
 * ordinary checker that logs its own `SafetyResult` (at `MAINSTEP`); without the demotion, any log
 * level from `MAINSTEP` on prints one result line per block analysis before DSS's own verdict, and
 * tools that read the verdict off the output (BenchExec's `theta-xcfa` tool-info takes the last
 * `SafetyResult` line, and only reports an error when there is none) would score a crashing DSS run
 * with the last block's result.
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
