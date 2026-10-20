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
package hu.bme.mit.theta.xcfa.cli.dss

import hu.bme.mit.theta.xcfa.analysis.dss.actor.*
import hu.bme.mit.theta.xcfa.cli.params.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertInstanceOf
import org.junit.jupiter.api.Test

class DefaultConfigsTest {

  @Test
  fun `default config is a predicate-domain CEGAR config`() {
    val config = getDefaultPredCegarConfig()

    assertEquals(Backend.CEGAR, config.backendConfig.backend)
    val cegarConfig = assertInstanceOf(CegarConfig::class.java, config.backendConfig.specConfig)
    assertEquals(Domain.PRED_CART, cegarConfig.abstractorConfig.domain)
  }

  @Test
  fun `building the default config twice does not share mutable state`() {
    val first = getDefaultPredCegarConfig()
    val second = getDefaultPredCegarConfig()

    (first.backendConfig.specConfig as CegarConfig).abstractorConfig.domain = Domain.PRED_SPLIT

    assertEquals(
      Domain.PRED_CART,
      (second.backendConfig.specConfig as CegarConfig).abstractorConfig.domain,
    )
  }
}
