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
package hu.bme.mit.theta.analysis.algorithm.mdd

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.analysis.algorithm.mdd.cegar.MddCegarChecker
import hu.bme.mit.theta.analysis.expr.refinement.createSeqItpCheckerFactory
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq
import hu.bme.mit.theta.core.type.anytype.Exprs.Prime
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntExprs.Lt
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.SolverStatus
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory
import org.junit.jupiter.api.Test

/**
 * Scratch: attributes every solver pool check() of the best config (constrained+seeded) to its call
 * site, bucketed as "origin <- driver" from the stack trace.
 */
class ScratchSolverCallSitesTest {

  private val siteCounts = HashMap<String, Int>()

  private inner class RecordingSolver(private val delegate: Solver) : Solver by delegate {
    override fun check(): SolverStatus {
      val stack = Thread.currentThread().stackTrace
      val status = delegate.check()
      val site = "${classify(stack)}  [${if (status.isSat) "sat" else "unsat"}]"
      synchronized(siteCounts) { siteCounts.merge(site, 1, Int::plus) }
      return status
    }
  }

  private inner class RecordingFactory(private val delegate: SolverFactory) : SolverFactory {
    override fun createSolver(): Solver = RecordingSolver(delegate.createSolver())

    override fun createUCSolver(): UCSolver = delegate.createUCSolver()

    override fun createItpSolver(): ItpSolver = delegate.createItpSolver()
  }

  // origin: the expression-node mechanism issuing the check; driver: the algorithm phase, the
  // highest-priority class found anywhere in the stack (innermost frame of that class)
  private val origins = listOf("Traverser", "MddExpressionRepresentation", "MddExpressionTemplate")
  private val drivers =
    listOf(
      "TraceProvider",
      "MddValuationCollector",
      "ReverseNextStateDescriptor",
      "MddExplicitRepresentationExtractor",
      "MddTransitionSeeding",
      "GeneralizedSaturationProvider",
      "SimpleSaturationProvider",
      "CursorGeneralizedSaturationProvider",
      "LegacyRelationalProductProvider",
      "CursorRelationalProductProvider",
      "MddIntersectionProvider",
      "MddUnionProvider",
      "MddMinusProvider",
      "MddInterpreter",
      "MddCegarChecker",
    )

  private fun classify(stack: Array<StackTraceElement>): String {
    fun label(f: StackTraceElement) =
      "${f.className.substringAfterLast('.').substringBefore('$')}.${f.methodName}:${f.lineNumber}"
    fun firstFrameOf(name: String): StackTraceElement? =
      stack.firstOrNull { it.className.substringAfterLast('.').substringBefore('$') == name }
    val origin = origins.firstNotNullOfOrNull(::firstFrameOf)?.let(::label) ?: "?"
    val driver = drivers.firstNotNullOfOrNull(::firstFrameOf)?.let(::label) ?: "?"
    return "$origin  <-  $driver"
  }

  private fun runBestConfig(
    name: String,
    init: Expr<BoolType>,
    tran: Expr<BoolType>,
    prop: Expr<BoolType>,
  ) {
    siteCounts.clear()
    SolverPool(RecordingFactory(Z3LegacySolverFactory.getInstance())).use { solverPool ->
      MddCegarChecker(
          MonolithicExpr(init, tran, prop),
          solverPool,
          NullLogger.getInstance(),
          createSeqItpCheckerFactory(Z3LegacySolverFactory.getInstance()),
          useReachConstraint = true,
          useTransitionSeeding = true,
        )
        .check(null)
      println("=== $name: total pool checks=${solverPool.checkCount} ===")
      siteCounts.entries
        .sortedByDescending { it.value }
        .forEach { (site, count) -> println("%5d  %s".format(count, site)) }
    }
  }

  @Test
  fun deepCex() {
    val x = Decls.Var("x", IntType.getInstance())
    runBestConfig(
      "deep cex: x'=x+1, x'<=10, !(x=10)",
      Eq(x.ref, Int(0)),
      And(Eq(Prime(x.ref), Add(x.ref, Int(1))), Leq(Prime(x.ref), Int(10))),
      Not(Eq(x.ref, Int(10))),
    )
  }

  @Test
  fun chain() {
    val x = Decls.Var("x", IntType.getInstance())
    val y = Decls.Var("y", IntType.getInstance())
    val z = Decls.Var("z", IntType.getInstance())
    runBestConfig(
      "chain: x'=y+1, y'=z+1, z'=z+1, z'<10, !(x=5)",
      And(Eq(x.ref, Int(0)), Eq(y.ref, Int(0)), Eq(z.ref, Int(0))),
      And(
        And(
          Eq(Prime(x.ref), Add(y.ref, Int(1))),
          Eq(Prime(y.ref), Add(z.ref, Int(1))),
          Eq(Prime(z.ref), Add(z.ref, Int(1))),
        ),
        Lt(Prime(z.ref), Int(10)),
      ),
      Not(Eq(x.ref, Int(5))),
    )
  }
}
