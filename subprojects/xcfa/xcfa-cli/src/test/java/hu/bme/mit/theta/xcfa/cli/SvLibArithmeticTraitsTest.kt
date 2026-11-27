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

import com.beust.jcommander.JCommander
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait.*
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.portfolio.getDefaultOutputConfig
import hu.bme.mit.theta.xcfa.cli.utils.getXcfa
import java.nio.file.Files
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class SvLibArithmeticTraitsTest {
  private fun traitsOf(
    locals: Map<String, String>,
    check: String,
    declarations: String = "",
  ): Set<ArithmeticTrait> {
    val script =
      """
      (set-logic ALL)
      $declarations
      (define-proc main () () (${locals.entries.joinToString(" ") { "(${it.key} ${it.value})" }})
        (sequence
          (havoc ${locals.keys.joinToString(" ")})
          (! (assume true) :tag t :check-true $check)))
      (verify-call main ())
      """
        .trimIndent()
    val input = Files.createTempFile("traits", ".svlib").toFile()
    input.deleteOnExit()
    input.writeText(script)
    val config =
      XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(
        inputConfig = InputConfig(input = input),
        frontendConfig = FrontendConfig(inputType = InputType.SVLIB),
        debugConfig = DebugConfig(debug = true),
      )
    val parseContext = ParseContext()
    getXcfa(config, parseContext, NullLogger.getInstance(), NullLogger.getInstance())
    return parseContext.arithmeticTraits
  }

  @Test
  fun linearIntegerArithmeticHasNoTraits() {
    val traits =
      traitsOf(
        mapOf("x" to "Int"),
        "(and (= (* 2 x) 4) (= (* (- 3) x) 6) (= (div x 3) 1) (= (mod x 2) 0))",
      )
    assertEquals(emptySet<ArithmeticTrait>(), traits)
  }

  @Test
  fun aProductOfVariablesIsNonlinear() {
    val traits = traitsOf(mapOf("x" to "Int", "y" to "Int"), "(not (= (* x y) 6))")
    assertTrue(NONLIN_INT in traits, "traits: $traits")
    assertTrue(NONCONST_DIV !in traits, "traits: $traits")
  }

  @Test
  fun aDivisionByAVariableIsNonlinear() {
    val traits = traitsOf(mapOf("x" to "Int", "y" to "Int"), "(not (= (div x y) 2))")
    assertTrue(NONLIN_INT in traits, "traits: $traits")
    assertTrue(NONCONST_DIV in traits, "traits: $traits")
  }

  @Test
  fun nonlinearRealArithmeticCountsAsNonlinear() {
    val traits = traitsOf(mapOf("r" to "Real", "s" to "Real"), "(not (> (* r s) r))")
    assertTrue(NONLIN_INT in traits, "traits: $traits")
    assertTrue(NONCONST_DIV !in traits, "traits: $traits")
  }

  @Test
  fun anUninterpretedFunctionIsNotAConstantFactor() {
    val traits =
      traitsOf(
        mapOf("x" to "Int"),
        "(not (= (* (f x) x) 6))",
        declarations = "(declare-fun f (Int) Int)",
      )
    assertTrue(NONLIN_INT in traits, "traits: $traits")
  }

  @Test
  fun bitvectorsAreBitwise() {
    val traits = traitsOf(mapOf("b" to "(_ BitVec 8)"), "(not (= (bvadd b b) #x01))")
    assertEquals(setOf(BITWISE), traits)
  }

  @Test
  fun floatingPointIsFloat() {
    val float = "(_ FloatingPoint 8 24)"
    val traits = traitsOf(mapOf("f" to float, "g" to float), "(fp.lt f g)")
    assertEquals(setOf(FLOAT), traits)
  }

  @Test
  fun aFloatReachedOnlyThroughAConversionIsFloat() {
    val traits = traitsOf(mapOf("b" to "(_ BitVec 32)"), "(not (fp.isNaN ((_ to_fp 8 24) b)))")
    assertEquals(setOf(FLOAT, BITWISE), traits)
  }

  @Test
  fun arraysAreArr() {
    val traits = traitsOf(mapOf("a" to "(Array Int Int)", "x" to "Int"), "(not (= (select a x) x))")
    assertEquals(setOf(ARR), traits)
  }

  @Test
  fun theSvLibWitnessFlagIsParsedAndReachesThePortfolioSteps() {
    val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>()
    JCommander.newBuilder()
      .apply { config.getObjects().forEach { addObject(it) } }
      .build()
      .parse("--enable-svlib-witness")
    assertTrue(config.outputConfig.svLibOutputConfig.generateWitness)
    assertTrue(getDefaultOutputConfig(config).svLibOutputConfig.generateWitness)
  }
}
