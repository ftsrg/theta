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
package hu.bme.mit.theta.xcfa.dss.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.solver.SolverManager
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaLastPrecProvider
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA

/**
 * The exact shape `xcfa-cli`'s `getCegarChecker` returns - but nothing in this module needs to know
 * that `getCegarChecker`, or `xcfa-cli`, exist at all:
 * [SafetyChecker]/[LocationInvariants]/[XcfaPrec] already live in lower modules
 * (`theta-analysis`/`xcfa-analysis`), so this alias is all [runWorkerConfig] needs to depend on.
 * Any [SafetyChecker] implementation fits here, not just a CEGAR one - a caller could substitute a
 * BMC-based checker, once one exists, with zero changes to DSS itself.
 */
typealias XcfaChecker =
  SafetyChecker<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>, XcfaPrec<*>>

/**
 * A function that builds an [XcfaChecker] for a given [XCFA] - the shape every DSS worker's
 * "ordinary, already-existing analysis" (plan §0/§3) takes. Named so
 * [DssCheckerRoster]/[DssCheckerSelectionStrategy] have something to hold a *list* of, instead of
 * every signature spelling out `(XCFA) -> XcfaChecker`.
 */
typealias CheckerFactory = (XCFA) -> XcfaChecker

/**
 * Runs [xcfa] through a checker [checkerFactory] builds for it, exactly as a standalone `xcfa-cli`
 * invocation with the same underlying config would - this *is* the "thin orchestration layer" piece
 * of the DSS plan (§0/§3): DSS does not reimplement predicate-abstraction CEGAR, a worker simply
 * forwards to an ordinary, already-existing analysis. For the `NO_DECOMPOSITION` case (build-order
 * step 3: the whole program is one block), this is the entire worker - there is no block-local
 * initial/target-state substitution to do, since there is only one block and no neighbours to
 * exchange postconditions/violation conditions with.
 *
 * [checkerFactory] is supplied by the caller rather than built in here (which is what this module
 * did through build-order step 8, calling `xcfa-cli`'s `getCegarChecker` directly with a fixed
 * predicate-CEGAR [hu.bme.mit.theta.xcfa.cli.params.XcfaConfig]) for two reasons: it decouples this
 * module from any *specific* checker or config type - the caller decides what "the ordinary,
 * already-existing analysis" actually is, CEGAR or otherwise - and it removes this module's
 * compile-time dependency on `xcfa-cli` entirely, which is what let `xcfa-cli` start depending on
 * DSS (build-order step 8's CLI integration) without creating a circular project dependency (this
 * module already needed `getCegarChecker` from `xcfa-cli`; `xcfa-cli` needing DSS back would have
 * closed the cycle). Callers that do want `xcfa-cli`'s real CEGAR checker still get it exactly the
 * same way - `getCegarChecker(xcfa, mcm, parseContext, config, logger)` - just supplied as the
 * factory from wherever `xcfa-cli` *is* on the classpath (production code behind `--algorithm DSS`,
 * or a test's own `testImplementation(project(":theta-xcfa-cli"))`), never required here.
 *
 * The caller must ensure solver names inside whatever config the factory captures (e.g. `"Z3"`) are
 * already resolvable through Theta's process-wide `SolverManager` registry before calling this -
 * exactly as a real `xcfa-cli` invocation's own startup would have done
 * (`ensureDefaultSolversRegistered`/`registerAllSolverManagers`, both in `xcfa-cli`).
 *
 * [initialPrecision], if given, is passed straight to the checker instead of letting it derive one
 * on its own. This matters once real block decomposition is involved (build-order step 5): a
 * config's own initial-precision derivation looks only at whatever XCFA is *checked* - for one
 * block extracted in isolation ([extractBlockXcfa]), that is only the block's own edges, which for
 * many blocks contain no assume/branch conditions of their own at all. Predicate-abstraction CEGAR
 * only refines precision in response to a counterexample it needs to refute; a block with nothing
 * to refute against never refines past whatever initial precision it started with, so with an empty
 * precision and no local branches, [packPostcondition] ends up packing the trivial, useless
 * `True()` for every such block - confirmed empirically while building this.
 * [globalAssumePredicatePrecision] (seeded from the *whole* original program's assume conditions,
 * not just one block's) is the validated fix: passed as [initialPrecision], it gives even a
 * branch-free block enough predicates to compute a precise summary at its exit.
 *
 * **No process-wide lock.** [checkerFactory] already builds a brand-new checker - and, inside it,
 * `getCegarChecker` already calls `SolverFactory.createSolver()` fresh - on every single call,
 * which means every call to this function already gets its own, never-shared Z3 `Solver` (and, one
 * layer down, its own native `Context`): see
 * [Z3SolverFactory][hu.bme.mit.theta.solver.z3.Z3SolverFactory] /`Z3LegacySolverFactory`'s
 * `createSolverInternal`, `new com.microsoft.z3.Context()` every time. Combined with the actor
 * runtime's one-thread-per-block model (`DssBlockActor` in `xcfa-dss-actor`, one dedicated platform
 * `Thread` for a block's entire lifetime), that means every solver this function ever creates is
 * both freshly-created *and* touched by exactly one thread for its whole life - no two blocks'
 * checks ever share a solver object, and no thread ever reaches into a solver another thread
 * created. This is this port's version of CPAchecker's own real answer to solver/thread affinity:
 * one thread owns one block's solver for that block's lifetime, letting genuine parallelism across
 * blocks replace this file's earlier single global lock.
 *
 * A process-wide lock here *did* crash the JVM outright the first time real, concurrent per-block
 * checks were tried without one (`EXCEPTION_ACCESS_VIOLATION` inside Z3's native library) - but the
 * actual, confirmed root cause turned out to be two ordinary, unsynchronized `java.util.HashSet`s
 * mutated by every single checker construction with no regard for which thread was calling:
 * `Z3SolverManager.instantiatedSolvers` (both the legacy and the new `solver-z3legacy`/`solver-z3`
 * managers) and `MonitorCheckpoint.registeredMonitors` (touched by `getCegarChecker`'s own
 * `MonitorCheckpoint.reset()`/`.register(...)` on every call, since `cexMonitor` defaults to
 * `CexMonitorOptions.CHECK`). Concurrent, unsynchronized mutation of a plain `HashSet` from several
 * threads at once is undefined behavior in the JVM - a real, confirmed bug regardless of what else
 * was going on, and hit on literally every checker construction. Both are now backed by
 * `ConcurrentHashMap.newKeySet()` instead.
 *
 * Fixing those two was **not** sufficient on its own, though - re-tested empirically, not assumed:
 * running the full concurrent suite with no lock at all still crashed the JVM
 * (`EXCEPTION_INT_DIVIDE_BY_ZERO` inside `libz3legacy.dll` this time, a different crash signature
 * than the original `EXCEPTION_ACCESS_VIOLATION` but the same underlying class of problem), which
 * means at least part of the original fragility genuinely is native, inside Z3's own legacy
 * binding, not just Theta's Java-level bookkeeping around it. What the codebase's own
 * solver-thread-affinity plan already suspected: Z3's native `Context` *construction* itself is not
 * safe to do concurrently from multiple threads at once, even though each resulting `Context` is
 * only ever touched by the one thread that created it afterward (Theta's
 * `Z3SolverFactory.createSolverInternal`/ `Z3LegacySolverFactory`'s equivalent, `new
 * com.microsoft.z3.Context()`, backed by shared native memory-management/parameter-registration
 * state under the hood).
 *
 * So the lock is narrowed, not removed: [checkerFactory] - the only place a fresh
 * `Solver`/`Context` gets created, since [runWorkerConfig] is called fresh per recheck and
 * `getCegarChecker` calls `SolverFactory.createSolver()` eagerly during construction - still runs
 * under a lock, but `checker.check(...)`, where all the actual, expensive ARG
 * exploration/abstraction/refinement work happens, now runs outside it. Different blocks' checkers
 * are still built one at a time, but once built, their solving genuinely proceeds in parallel -
 * real parallelism for the overwhelming majority of the work, with only the comparatively cheap act
 * of standing up a new `Context` serialized to stay inside whatever discipline the native library
 * actually needs. Confirmed via repeated stress runs of the full concurrent suite
 * (`xcfa-dss-actor`'s cyclic/nested/merge/diverse-program tests) with no further native crashes -
 * see `doc/DSS.md`.
 */
private val solverConstructionLock = Any()

/**
 * Runs [construct] under the same lock as checker construction in [runWorkerConfig] - for anything
 * else in DSS that creates a native solver context (e.g. [DssPredicateOperators]).
 */
fun <T> withSolverConstructionLock(construct: () -> T): T =
  synchronized(solverConstructionLock) { construct() }

/**
 * [onLastPrec], if given, receives the precision the checker ended with - only from checkers that
 * report one ([XcfaLastPrecProvider], i.e. CEGAR), and only once the check is done.
 */
fun runWorkerConfig(
  xcfa: XCFA,
  checkerFactory: CheckerFactory,
  initialPrecision: XcfaPrec<*>? = null,
  onLastPrec: ((XcfaPrec<*>) -> Unit)? = null,
): SafetyResult<LocationInvariants, Trace<XcfaState<PtrState<*>>, XcfaAction>> {
  // Every solver the checker creates is closed once the check is done (and under the same lock as
  // construction): solver managers otherwise keep each one alive until SolverManager.closeAll(),
  // and DSS builds a fresh checker for every single block analysis.
  return SolverManager.withSolverScope(solverConstructionLock) {
    val checker = withSolverConstructionLock { checkerFactory(xcfa) }
    val result = if (initialPrecision != null) checker.check(initialPrecision) else checker.check()
    if (onLastPrec != null) (checker as? XcfaLastPrecProvider)?.lastPrec?.let(onLastPrec)
    result
  }
}
