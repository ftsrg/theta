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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.params.CFrontendConfig
import hu.bme.mit.theta.xcfa.cli.portfolio.ConfigNode
import hu.bme.mit.theta.xcfa.cli.portfolio.Node
import hu.bme.mit.theta.xcfa.cli.portfolio.STM
import hu.bme.mit.theta.xcfa.cli.portfolio.complex27
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertNotEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * The COMPLEX27 chain is ordered and budgeted from measurement, so these lock in the properties
 * that measurement paid for: which configuration runs first, that the slices fit the competition's
 * limit, and that a solver failure is absorbed by a different solver rather than by skipping ahead.
 */
class Complex27ChainTest {

  private val budgetMs = 900_000L

  /** A single procedure whose control flow loops back, so the program is not loop-free. */
  private fun looping() =
    xcfa("") {
        val main =
          procedure("main") {
            "x" type Int()
            (init to "L0") { "x".assign("0") }
            ("L0" to "L0") { "x".assign("(+ x 1)") }
            ("L0" to final) { assume("(= x 3)") }
          }
        main.start()
      }
      .let { it }

  /** The same program with the back edge removed. */
  private fun loopFree() =
    xcfa("") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "L0") { "x".assign("0") }
          ("L0" to final) { assume("(= x 0)") }
        }
      main.start()
    }

  /** Dereferences something, so the trait chain resolves to PTR rather than BITWISE. */
  private fun pointerProgram() =
    xcfa("") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "L0") { "x".assign("(deref 1 0 Int)") }
          ("L0" to "L0") { "x".assign("(+ x 1)") }
          ("L0" to final) { assume("(= x 3)") }
        }
      main.start()
    }

  private fun stmFor(
    program: XCFA,
    parseContext: ParseContext = ParseContext(),
    property: ErrorDetection = ErrorDetection.ERROR_LOCATION,
  ): STM =
    complex27(
      program,
      emptySet(),
      parseContext,
      XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(
        inputConfig = InputConfig(property = XcfaProperty(property)),
        debugConfig = DebugConfig(debug = true),
      ),
      NullLogger.getInstance(),
      NullLogger.getInstance(),
    )

  /** Config names down the timeout path, which is the order a run actually experiences. */
  private fun chain(stm: STM): List<String> {
    val order = mutableListOf<String>()
    var node: Node? = stm.initNode
    val seen = mutableSetOf<Node>()
    while (node != null && seen.add(node)) {
      if (node is ConfigNode) order.add(node.name)
      node = node.outEdges.firstOrNull { it.trigger.toString() != "SolverError" }?.target
    }
    return order
  }

  private fun timeouts(stm: STM): List<Long> =
    chain(stm).mapNotNull { name ->
      nodesOf(stm).firstOrNull { it.name == name }?.config?.backendConfig?.timeoutMs
    }

  private fun nodesOf(stm: STM): Set<ConfigNode> {
    val all = mutableSetOf<Node>()
    val queue = ArrayDeque(listOf(stm.initNode))
    while (queue.isNotEmpty()) {
      val n = queue.removeFirst()
      if (!all.add(n)) continue
      n.outEdges.forEach { queue.addLast(it.target) }
    }
    return all.filterIsInstance<ConfigNode>().toSet()
  }

  @Test
  fun aFloatProgramLeadsWithKInduction() {
    // Over the float tasks k-induction solves about three times what the predicate lead does, and
    // the predicate configurations add nothing on top of it -- the opposite of the whole-suite
    // order, where k-induction is fourth.
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.FLOAT) }
    val order = chain(stmFor(looping(), ctx))
    assertTrue(order.first().startsWith("KIND"), "float chain led with ${order.first()}")
    assertFalse(
      order.take(3).any { it.startsWith("PRED_CART") },
      "a predicate configuration still runs early on floats: $order",
    )
  }

  @Test
  fun aFloatProgramGivesKInductionTheLeadSlice() {
    // The wins it picks up need 80-110s; at a later position it would only ever get the shorter
    // follow-up slice.
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.FLOAT) }
    val stm = stmFor(looping(), ctx)
    val budgets = timeouts(stm)
    assertTrue(
      budgets.first() > budgets[1],
      "the leading configuration did not get the lead slice: $budgets",
    )
  }

  @Test
  fun theStrongestConfigurationRunsFirstAndBmcSecond() {
    // Measured marginal contribution over the whole suite, and identically in both the bitvector
    // and the integer half of the sweep: PRED_CART/BW_BIN_ITP alone solves the most, and BMC adds
    // more on top of it than any other algorithm.
    val order = chain(stmFor(looping()))
    assertTrue(order.first().startsWith("PRED_CART-BW_BIN_ITP"), "first was ${order.first()}")
    assertTrue(order[1].startsWith("BMC"), "second was ${order[1]}")
  }

  @Test
  fun aLoopFreeProgramLeadsWithTheBoundedEngines() {
    // With no cycle every execution is finite, so a bounded check that reaches the longest path is
    // a proof rather than a guess -- the engines that can finish go first.
    val order = chain(stmFor(loopFree()))
    assertTrue(order.first().startsWith("BMC"), "first was ${order.first()}")
    assertTrue(order[1].startsWith("KIND"), "second was ${order[1]}")
  }

  @Test
  fun nonLinearArithmeticLeadsWithTheBoundedEngines() {
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.NONLIN_INT) }
    val order = chain(stmFor(looping(), ctx))
    assertTrue(order.first().startsWith("BMC"), "first was ${order.first()}")
  }

  @Test
  fun theChainFitsTheCompetitionBudget() {
    // The previous chain handed out 950 s of slices inside a 900 s limit, so its last configuration
    // could never run.
    listOf(looping(), loopFree()).forEach { program ->
      val total = timeouts(stmFor(program)).sum()
      assertTrue(total <= budgetMs, "chain budget was $total ms for $program")
    }
  }

  /**
   * A program with pointers *and* bitwise operators takes the pointer chain but is encoded over
   * bitvectors, and `PTR` is tested before `BITWISE`, so this is the common case rather than a
   * corner one. Z3's legacy API is the only Z3 that interpolates and it refuses bitvectors, so
   * keying the solver off the chain instead of the encoding wasted every interpolating slice.
   */
  @Test
  fun aPointerProgramWithBitwiseOpsInterpolatesOnABitvectorCapableSolver() {
    val ctx =
      ParseContext().apply {
        addArithmeticTrait(ArithmeticTrait.BITWISE)
        arithmetic = ArithmeticType.bitvector
      }
    val interpolating =
      nodesOf(stmFor(pointerProgram(), ctx)).filter { "ITP" in it.name && "BMC" !in it.name }
    assertTrue(interpolating.isNotEmpty(), "no interpolating configuration in the chain")
    interpolating.forEach {
      // MathSAT and Bitwuzla both interpolate over bitvectors; the legacy Z3 API does not.
      assertTrue(
        it.name.contains("mathsat") || it.name.contains("bitwuzla"),
        "interpolating on a solver that refuses bitvectors: ${it.name}",
      )
    }
  }

  /**
   * MathSAT refuses floats and bitvectors together ("FP<->BV combination unsupported"), so a
   * program carrying both has to go to cvc5 even though bitvectors alone would pick MathSAT.
   */
  @Test
  fun floatsAndBitvectorsTogetherGoToCvc5() {
    val ctx =
      ParseContext().apply {
        addArithmeticTrait(ArithmeticTrait.FLOAT)
        addArithmeticTrait(ArithmeticTrait.BITWISE)
        arithmetic = ArithmeticType.bitvector
      }
    val interpolating =
      nodesOf(stmFor(pointerProgram(), ctx)).filter { "ITP" in it.name && "BMC" !in it.name }
    assertTrue(interpolating.isNotEmpty())
    interpolating.forEach {
      assertTrue(it.name.contains("cvc5"), "float+bitvector must use cvc5: ${it.name}")
    }
  }

  @Test
  fun aBitwiseProgramNeverInterpolatesOnZ3() {
    // Z3's legacy API is the only Z3 that interpolates, and it refuses bitvectors outright
    // ("theory not supported by interpolation"). An interpolating configuration on Z3 is therefore
    // a wasted slice for every bitwise program.
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.BITWISE) }
    val interpolating =
      nodesOf(stmFor(looping(), ctx)).filter { "ITP" in it.name && "BMC" !in it.name }
    assertTrue(interpolating.isNotEmpty(), "no interpolating configuration in the chain")
    interpolating.forEach {
      // MathSAT and Bitwuzla both interpolate over bitvectors; the legacy Z3 API does not.
      assertTrue(
        it.name.contains("mathsat") || it.name.contains("bitwuzla"),
        "interpolating on a solver that refuses bitvectors: ${it.name}",
      )
    }
  }

  @Test
  fun everyConfigurationHasASolverTwinOnADifferentSolver() {
    // A solver failure is a property of the solver, not of the program, so it must not cost the
    // next algorithm its slice.
    val stm = stmFor(looping())
    val withTwin =
      nodesOf(stm).filter { node -> node.outEdges.any { it.trigger.toString() == "SolverError" } }
    assertTrue(withTwin.isNotEmpty(), "no solver fallback edges at all")
    withTwin.forEach { node ->
      val twin = node.outEdges.first { it.trigger.toString() == "SolverError" }.target
      assertNotEquals(node.name, twin.name, "solver twin of ${node.name} is itself")
      val family = { n: String -> n.substringBeforeLast("-").substringBeforeLast("-") }
      assertEquals(family(node.name), family(twin.name), "twin changes more than the solver")
    }
  }

  private fun arithmeticOf(node: ConfigNode): ArithmeticType? =
    (node.config.frontendConfig.specConfig as? CFrontendConfig)?.arithmetic

  @Test
  fun theLastSliceRetriesUnderTheOtherEncoding() {
    // `efficient` resolves to integer wherever integer can express the program, and on the tasks
    // both encodings can parse integer solves more in every algorithm measured. Bitvector still
    // decides several hundred per algorithm that integer cannot, so the final slice re-reads the
    // program under it rather than spending the budget on a sixth algorithm.
    val stm = stmFor(looping())
    // The COMPLEX portfolio is appended after the chain as a catch-all; the encoding retry is the
    // last configuration this portfolio chooses itself.
    val lastOwn = chain(stm).last { !it.startsWith("Complex") }
    val last = nodesOf(stm).first { it.name == lastOwn }
    assertEquals(ArithmeticType.bitvector, arithmeticOf(last), "last slice was ${last.name}")
    assertTrue(last.config.inputConfig.xcfaWCtx == null, "the retry must re-parse, not reuse")
    assertTrue(last.name.contains("mathsat"), "bitvector interpolation needs MathSAT: ${last.name}")
  }

  @Test
  fun aBitwiseProgramDoesNotPayForAnEncodingRetry() {
    // `efficient` has already resolved to bitvector for a bitwise program, so re-parsing under
    // bitvector would rebuild the same XCFA and spend the slice for nothing.
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.BITWISE) }
    val stm = stmFor(looping(), ctx)
    assertTrue(
      nodesOf(stm).none { arithmeticOf(it) == ArithmeticType.bitvector },
      "a bitwise program should not re-parse under bitvector",
    )
  }

  @Test
  fun aFloatProgramDoesNotRetryUnderBitvector() {
    // Floats have no bitvector encoding to fall back to.
    val ctx = ParseContext().apply { addArithmeticTrait(ArithmeticTrait.FLOAT) }
    val stm = stmFor(looping(), ctx)
    assertTrue(nodesOf(stm).none { arithmeticOf(it) == ArithmeticType.bitvector })
  }

  /**
   * Measured over the whole suite, the property separates the algorithms better than any syntactic
   * trait: on memory safety the explicit domain solves nearly twice what the strongest predicate
   * configuration does, because a memory-safety proof turns on the concrete cells an access can
   * reach.
   */
  @Test
  fun memorySafetyLeadsWithTheExplicitDomain() {
    val order = chain(stmFor(looping(), property = ErrorDetection.MEMSAFETY))
    assertTrue(order.first().startsWith("EXPL-SEQ_ITP"), "first was ${order.first()}")
  }

  /** Reachability keeps the predicate leader, which is the strongest configuration there. */
  @Test
  fun reachabilityKeepsThePredicateLeader() {
    val order = chain(stmFor(looping(), property = ErrorDetection.ERROR_LOCATION))
    assertTrue(order.first().startsWith("PRED_CART-BW_BIN_ITP"), "first was ${order.first()}")
  }

  /** A wide, branchy procedure: past a McCabe complexity of ~16 the explicit domain overtakes. */
  private fun complexProgram() =
    xcfa("") {
      val main =
        procedure("main") {
          "x" type Int()
          (init to "L0") { "x".assign("0") }
          (0 until 40).forEach { i -> ("L0" to "L$i") { assume("(= x $i)") } }
          (0 until 40).forEach { i -> ("L$i" to final) { "x".assign("$i") } }
        }
      main.start()
    }

  @Test
  fun aComplexProgramLeadsWithTheExplicitDomain() {
    // Measured over the whole suite: below ~16 the predicate domains lead, above it the explicit
    // domain does, and the gap widens with size.
    val order = chain(stmFor(complexProgram()))
    assertTrue(order.first().startsWith("EXPL-SEQ_ITP"), "first was ${order.first()}")
  }

  @Test
  fun aSmallProgramKeepsThePredicateLeader() {
    val order = chain(stmFor(looping()))
    assertTrue(order.first().startsWith("PRED_CART-BW_BIN_ITP"), "first was ${order.first()}")
  }
}
