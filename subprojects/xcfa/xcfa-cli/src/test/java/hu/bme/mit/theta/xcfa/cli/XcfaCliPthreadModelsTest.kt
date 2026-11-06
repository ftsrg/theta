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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel
import java.io.File
import java.nio.file.Path
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.api.io.TempDir
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class XcfaCliPthreadModelsTest {
  @TempDir lateinit var tempDir: Path

  companion object {
    @JvmStatic
    fun programs(): Stream<Arguments> {
      val programs =
        listOf(
          "pthread_tls_basic_safe.c" to true,
          "pthread_tls_isolation_unsafe.c" to false,
          "pthread_tls_fresh_keys_safe.c" to true,
          "pthread_barrier_capacity_unsafe.c" to false,
          "pthread_barrier_reuse_unsafe.c" to false,
          "pthread_barrier_serial_early_unsafe.c" to false,
          "pthread_barrier_serial_unique_safe.c" to true,
        )
      return programs
        .flatMap { (file, safe) ->
          listOf(POR.NOPOR, POR.SPOR, POR.AASPOR).map { por ->
            Arguments.of(file, safe, por, ArithmeticType.efficient)
          }
        }
        .plus(
          listOf("pthread_tls_basic_safe.c", "pthread_tls_fresh_keys_safe.c").map {
            Arguments.of(it, true, POR.AASPOR, ArithmeticType.bitvector)
          }
        )
        .stream()
    }
  }

  @ParameterizedTest(name = "{0}, {2}, {3}")
  @MethodSource("programs")
  @Timeout(60)
  fun cegarVerdict(file: String, safe: Boolean, por: POR, arithmetic: ArithmeticType) {
    val logger = NullLogger.getInstance()
    val config =
      XcfaConfig<CFrontendConfig, CegarConfig>(
        inputConfig =
          InputConfig(input = File(javaClass.getResource("/c/pthread-models/$file")!!.toURI())),
        frontendConfig =
          FrontendConfig(
            lbeLevel = LbeLevel.LBE_LOCAL,
            specConfig =
              CFrontendConfig(
                arithmetic = arithmetic,
                architecture =
                  if (file == "pthread_barrier_capacity_unsafe.c") ArchitectureType.LP64
                  else ArchitectureType.ILP32,
              ),
          ),
        backendConfig =
          BackendConfig(
            backend = Backend.CEGAR,
            solverHome = tempDir.resolve("solvers").toString(),
            specConfig =
              CegarConfig(
                por = por,
                abstractorConfig =
                  CegarAbstractorConfig(
                    domain =
                      if (file == "pthread_barrier_serial_unique_safe.c") Domain.PRED_BOOL
                      else Domain.PRED_CART,
                    maxEnum = 1,
                    search = Search.DFS,
                  ),
                refinerConfig =
                  CegarRefinerConfig(
                    refinement = Refinement.SEQ_ITP,
                    exprSplitter = ExprSplitterOptions.ATOMS,
                    pruneStrategy = PruneStrategy.FULL,
                  ),
              ),
          ),
        outputConfig = OutputConfig(enabled = OutputLevel.NONE, resultFolder = tempDir.toFile()),
      )
    val result = runConfig(config, logger, logger, true) as SafetyResult<*, *>
    assertEquals(safe, result.isSafe, "$file: $result")
    assertEquals(!safe, result.isUnsafe, "$file: $result")
  }
}
