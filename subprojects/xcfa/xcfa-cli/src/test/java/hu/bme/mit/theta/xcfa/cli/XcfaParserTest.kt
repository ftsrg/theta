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
import hu.bme.mit.theta.common.logging.UniqueWarningLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.cli.params.FrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.InputConfig
import hu.bme.mit.theta.xcfa.cli.params.InputType
import hu.bme.mit.theta.xcfa.cli.params.SpecBackendConfig
import hu.bme.mit.theta.xcfa.cli.params.SpecFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getXcfa
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Test
import java.io.File

class XcfaParserTest {

  @Test
  fun parsesSvLibInputThroughMainXcfaParser() {
    val resource = javaClass.classLoader.getResource("svlib/check-true-annotate-tag.svlib")
    val input = File(requireNotNull(resource).toURI())
    val logger = NullLogger.getInstance()

    val xcfa =
      getXcfa(
        XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(
          inputConfig = InputConfig(input = input),
          frontendConfig = FrontendConfig(inputType = InputType.SVLIB),
        ),
        ParseContext(),
        logger,
        UniqueWarningLogger(logger),
      )

    assertEquals("SvLibXCFA", xcfa.name)
    assertFalse(xcfa.procedures.isEmpty())
  }
}
