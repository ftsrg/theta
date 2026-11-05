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

import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType.ILP32
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType.flat
import hu.bme.mit.theta.xcfa.ErrorDetection.DATA_RACE
import hu.bme.mit.theta.xcfa.ErrorDetection.ERROR_LOCATION
import hu.bme.mit.theta.xcfa.WitnessInfo
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.passes.LbePass.LbeLevel.NO_LBE
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import java.io.File
import kotlinx.serialization.builtins.ListSerializer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test

class XcfaConfigSerializationTest {

  @Test
  fun testWitnessPropertyRoundTrip() {
    val witnessFile =
      File(javaClass.getResource("/c/witness-validation/concurrent-unreach.witness.yml")!!.toURI())
    val witness =
      WitnessYamlConfig.decodeFromString(
          ListSerializer(YamlWitness.serializer()),
          witnessFile.readText(),
        )[0]
    val property = XcfaProperty(DATA_RACE, WitnessInfo(witness) { error("not applied") })
    property.transformSpecification(ERROR_LOCATION)
    val config =
      XcfaConfig(
        inputConfig =
          InputConfig(input = File("task.c"), witness = witnessFile, property = property),
        frontendConfig =
          FrontendConfig(
            lbeLevel = NO_LBE,
            loopUnroll = 7,
            specConfig = CFrontendConfig(architecture = ILP32, memoryModel = flat),
          ),
        backendConfig =
          BackendConfig(
            backend = Backend.CEGAR,
            timeoutMs = 1234,
            inProcess = true,
            specConfig =
              CegarConfig(
                por = POR.SPOR,
                abstractorConfig = CegarAbstractorConfig(domain = Domain.PRED_CART),
              ),
          ),
      )

    val json = config.toJson()
    val decoded = xcfaConfigFromJson(json)

    assertEquals(json, decoded.toJson())
    assertEquals(config.frontendConfig, decoded.frontendConfig)
    assertEquals(config.backendConfig, decoded.backendConfig)
    assertEquals(config.outputConfig, decoded.outputConfig)
    assertEquals(config.debugConfig, decoded.debugConfig)
    assertEquals(witnessFile, decoded.inputConfig.witness)
    assertEquals(DATA_RACE, decoded.inputConfig.property.inputProperty)
    assertEquals(ERROR_LOCATION, decoded.inputConfig.property.verifiedProperty)
    assertNull(decoded.inputConfig.property.witness)
  }

  @Test
  fun testAllSpecConfigsRoundTrip() {
    Backend.entries.forEach { backend ->
      val backendConfig = BackendConfig<SpecBackendConfig>(backend = backend)
      backendConfig.createSpecConfig()
      val config = XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(backendConfig = backendConfig)
      assertEquals(config.backendConfig, xcfaConfigFromJson(config.toJson()).backendConfig)
    }
    InputType.entries.forEach { inputType ->
      val frontendConfig = FrontendConfig<SpecFrontendConfig>(inputType = inputType)
      frontendConfig.createSpecConfig()
      val config =
        XcfaConfig<SpecFrontendConfig, SpecBackendConfig>(frontendConfig = frontendConfig)
      assertEquals(config.frontendConfig, xcfaConfigFromJson(config.toJson()).frontendConfig)
    }
  }
}
