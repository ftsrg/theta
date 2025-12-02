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

import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import java.util.stream.Stream
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.exists
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.provider.Arguments

data class WitnessEdge(
  val startlineRange: Pair<Int, Int>?,
  val endlineRange: Pair<Int, Int>?,
  val startoffsetRange: Pair<Int, Int>?,
  val endoffsetRange: Pair<Int, Int>?,
  val assumption: Regex?,
)

class XcfaCliProofTest {
  companion object {

    @JvmStatic
    fun cFiles(): Stream<Arguments> {
      return Stream.of(
        Arguments.of(
          "/c/litmustest/singlethread/witness_test.c",
          null,
          listOf(
            WitnessEdge(
              startlineRange = Pair(5, 5),
              endlineRange = Pair(5, 5),
              startoffsetRange = Pair(80, 90),
              endoffsetRange = Pair(112, 122),
              assumption = Regex("i *== *-1"),
            )
          ),
        ),
        Arguments.of(
          "/c/litmustest/singlethread/witness_test.c",
          "--backend BOUNDED",
          listOf(
            WitnessEdge(
              startlineRange = Pair(5, 5),
              endlineRange = Pair(5, 5),
              startoffsetRange = Pair(80, 90),
              endoffsetRange = Pair(112, 122),
              assumption = Regex("i *== *-1"),
            )
          ),
        ),
      )
    }
  }

  //  @ParameterizedTest
  //  @MethodSource("cFiles")
  fun testCWitness(filePath: String, extraArgs: String?, expectedWitnessEdges: List<WitnessEdge>) {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--output",
        "ALL",
        "--input-type",
        "C",
        "--input",
        javaClass.getResource(filePath)!!.path,
        *(extraArgs?.split(" ")?.toTypedArray() ?: emptyArray()),
        "--stacktrace",
        "--output-directory",
        temp.absolutePathString(),
        "--debug",
      )
    main(params)
    Assertions.assertTrue(temp.resolve("witness.graphml").exists())
    val witnessContents = temp.resolve("witness.graphml").toFile().readText()
    val edges = mutableListOf<Map<String, String>>()
    val edgeMatcher = Regex("(?s)<edge.*?</edge")
    for (match in edgeMatcher.findAll(witnessContents)) {
      val dataMatcher = Regex("<data key=\"(.*)\">(.*)</data>")
      val data = mutableMapOf<String, String>()
      for (dataMatch in dataMatcher.findAll(match.value)) {
        val (key, value) = dataMatch.destructured
        data.put(key, value)
      }
      edges.add(data)
      println(
        "Found edge containing data: ${data.entries.map { "${it.key}: ${it.value}" }.joinToString(", ")}"
      )
    }
    for (expectedWitnessEdge in expectedWitnessEdges) {
      Assertions.assertFalse(
        edges.none { edge ->
          val startline =
            expectedWitnessEdge.startlineRange
              ?.let { edge["startline"]?.let { v -> Pair(it, Integer.parseInt(v)) } }
              ?.let { it.first.first <= it.second && it.second <= it.first.second } ?: false
          val endline =
            expectedWitnessEdge.endlineRange
              ?.let { edge["endline"]?.let { v -> Pair(it, Integer.parseInt(v)) } }
              ?.let { it.first.first <= it.second && it.second <= it.first.second } ?: false
          val startoffset =
            expectedWitnessEdge.startoffsetRange
              ?.let { edge["startoffset"]?.let { v -> Pair(it, Integer.parseInt(v)) } }
              ?.let { it.first.first <= it.second && it.second <= it.first.second } ?: false
          val endoffset =
            expectedWitnessEdge.endoffsetRange
              ?.let { edge["endoffset"]?.let { v -> Pair(it, Integer.parseInt(v)) } }
              ?.let { it.first.first <= it.second && it.second <= it.first.second } ?: false
          val assumption =
            expectedWitnessEdge.assumption
              ?.let { edge["assumption"]?.let { v -> Pair(it, v) } }
              ?.let { it.first.matches(it.second) } ?: false
          startline && endline && startoffset && endoffset && assumption
        },
        "Expected witness edge not found: $expectedWitnessEdge",
      )
    }
    temp.toFile().deleteRecursively()
  }
}
