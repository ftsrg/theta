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

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.ptr.PtrPrec
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.CheckerFactory
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DeadlineSolverManager
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.XcfaChecker
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.hasQuantifier
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.isDssBudgetExceeded
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withQuantifierFreePrecondition
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.withSolverConstructionLock
import hu.bme.mit.theta.xcfa.cli.params.Backend
import hu.bme.mit.theta.xcfa.cli.params.BoundedConfig
import hu.bme.mit.theta.xcfa.cli.params.DssCegarDomain
import hu.bme.mit.theta.xcfa.cli.params.DssConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig

/**
 * The block checkers of [dssConfig], in roster order: `--dss-checker-backends`, then the EXPL
 * checker. With a budget they run on [DeadlineSolverManager] solvers; with a fallback solver each
 * is retried once on it.
 */
internal fun blockCheckers(
  dssConfig: DssConfig,
  solver: String,
  checkerFor: (backend: Backend, domain: DssCegarDomain, blockSolver: String?) -> CheckerFactory,
): List<CheckerFactory> {
  val budgeted = dssConfig.checkerBudgetMs > 0
  fun blockSolver(name: String): String {
    if (!budgeted) return name
    DeadlineSolverManager.ensureRegistered(name)
    return DeadlineSolverManager.nameFor(name)
  }
  val primary = if (budgeted) blockSolver(solver) else dssConfig.solver
  val fallback = dssConfig.fallbackSolver?.let(::blockSolver)
  val entries =
    dssConfig.checkerBackends.map { it to dssConfig.cegarDomain } +
      listOfNotNull((Backend.CEGAR to DssCegarDomain.EXPL).takeIf { dssConfig.explChecker })
  return entries.map { (backend, domain) ->
    val main = checkerFor(backend, domain, primary)
    if (fallback == null) main else withSolverFallback(main, checkerFor(backend, domain, fallback))
  }
}

/** Points every solver of a bounded checker's config at [solver]. */
internal fun XcfaConfig<*, *>.useSolver(solver: String) {
  val bounded = backendConfig.specConfig as BoundedConfig
  bounded.bmcConfig.bmcSolver = solver
  bounded.indConfig.indSolver = solver
  bounded.itpConfig.itpSolver = solver
}

/**
 * [primary], and if it throws, [fallback] once; a budget overrun or an interruption is passed on,
 * as the budget belongs to the block analysis, not to the solver.
 *
 * The fallback gets the block without quantifiers in its precondition and its precision: they come
 * from `Z3:new` interpolants, and a fallback solver without quantifiers (MathSAT) fails on them. A
 * weaker precondition and a smaller precision keep the block's result sound
 * ([withQuantifierFreePrecondition]).
 */
internal fun withSolverFallback(primary: CheckerFactory, fallback: CheckerFactory): CheckerFactory =
  { xcfa ->
    val first = primary(xcfa)
    object : XcfaChecker {
      override fun check() = attempt({ it.check() }, { it.check() })

      override fun check(input: XcfaPrec<*>?) =
        attempt({ it.check(input) }, { it.check(withoutQuantifiedPredicates(input)) })

      private fun <R> attempt(run: (XcfaChecker) -> R, rerun: (XcfaChecker) -> R): R =
        try {
          run(first)
        } catch (e: Exception) {
          if (e is InterruptedException || e.isDssBudgetExceeded()) throw e
          val second = withSolverConstructionLock { fallback(withQuantifierFreePrecondition(xcfa)) }
          try {
            rerun(second)
          } catch (f: Exception) {
            f.addSuppressed(e)
            throw f
          }
        }
    }
  }

/** [prec] without its quantified predicates; other precisions are returned as they are. */
internal fun withoutQuantifiedPredicates(prec: XcfaPrec<*>?): XcfaPrec<*>? {
  val ptr = prec?.p as? PtrPrec<*> ?: return prec
  val pred = ptr.innerPrec as? PredPrec ?: return prec
  if (pred.preds.none(::hasQuantifier)) return prec
  val kept = PredPrec.of(pred.preds.filterNot(::hasQuantifier))
  return XcfaPrec(PtrPrec(kept, ptr.set, ptr.smth), prec.noPop)
}
