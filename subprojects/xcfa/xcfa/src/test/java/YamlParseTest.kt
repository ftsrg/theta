/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import com.charleskorn.kaml.Yaml
import hu.bme.mit.theta.xcfa.cli.witnesses.*
import java.util.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

class YamlParseTest {
  @Test
  fun serialize() {
    val witness =
      YamlWitness(
        entryType = EntryType.VIOLATION,
        metadata =
          Metadata(
            formatVersion = "2.0",
            uuid = UUID.randomUUID().toString(),
            creationTime = getIsoDate(),
            producer = Producer(name = "test", version = "1.0.0"),
            task =
              Task(
                inputFiles = listOf("example.c"),
                inputFileHashes = mapOf(Pair("example.c", "hash")),
                specification = "unreach_call",
                dataModel = DataModel.LP64,
                language = Language.C,
              ),
          ),
        content =
          listOf(
            ContentItem(
              WaypointContent(
                type = WaypointType.ASSUMPTION,
                constraint = Constraint(value = "1 < x", format = Format.C_EXPRESSION),
                location = Location(fileName = "example.c", line = 15),
                action = Action.FOLLOW,
              )
            )
          ),
      )

    val result = WitnessYamlConfig.encodeToString(YamlWitness.serializer(), witness)

    System.err.println(result)

    val parsedPack = Yaml.default.decodeFromString(YamlWitness.serializer(), result)

    Assertions.assertEquals(witness, parsedPack)
  }
}
