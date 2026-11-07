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

import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness
import kotlinx.serialization.builtins.ListSerializer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class WitnessUnrollBoundTest {

  private fun waypoint(line: Int, threadId: Int) =
    """
  - segment:
    - waypoint:
        type: 'assumption'
        constraint:
          value: '1'
          format: 'c_expression'
        location:
          file_name: 'a.c'
          line: $line
          column: 3
        action: 'follow'
        thread_id: $threadId
"""

  private fun witness(vararg waypoints: Pair<Int, Int>): YamlWitness =
    WitnessYamlConfig.decodeFromString(
        ListSerializer(YamlWitness.serializer()),
        """
- entry_type: 'violation_sequence'
  metadata:
    format_version: '2.2'
    uuid: '00000000-0000-0000-0000-000000000000'
    creation_time: '2026-01-01T00:00:00Z'
    producer:
      name: 'test'
      version: '1'
    task:
      input_files:
      - 'a.c'
      input_file_hashes:
        'a.c': '0'
      specification: 'CHECK( init(main()), LTL(G ! data-race) )'
      data_model: 'ILP32'
      language: 'C'
  content:
"""
          .trimStart() + waypoints.joinToString("") { (line, tid) -> waypoint(line, tid) },
      )[0]

  @Test
  fun locationsOfDifferentThreadsAreCountedSeparately() {
    // every thread passes line 10 once, only thread 1 passes line 20 twice
    val w = witness(10 to 0, 10 to 1, 10 to 2, 20 to 1, 20 to 1)
    assertEquals(1, witnessUnrollBound(w))
  }
}
