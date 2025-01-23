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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.enum
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.common.table.BasicTableWriter

class XstsCliHeader : CliktCommand(name = "header") {

  private val writer = BasicTableWriter(System.out, ",", "\"", "\"")

  enum class Algorithm {
    CEGAR,
    MDD,
    BOUNDED,
    PN_MDD,
    CHC,
  }

  private val algorithm: Algorithm by
    option(help = "The algorithm to print the header for").enum<Algorithm>().required()
  private val iterationStrategy: MddChecker.IterationStrategy by
    option(help = "The state space generation algorithm for symbolic checking")
      .enum<MddChecker.IterationStrategy>()
      .default(MddChecker.IterationStrategy.GSAT)

  override fun run() {
    when (algorithm) {
      Algorithm.CEGAR -> printCegarHeader()
      Algorithm.BOUNDED -> printBoundedHeader()
      Algorithm.MDD -> printMddHeader()
      Algorithm.PN_MDD -> printSymbolicHeader()
      Algorithm.CHC -> printChcHeader()
    }
  }

  private fun printCommonHeader() {
    listOf("Result", "TimeMs", "CexLen", "Vars").forEach(writer::cell)
  }

  private fun printCegarHeader() {
    printCommonHeader()
    listOf(
        "AlgoTimeMs",
        "AbsTimeMs",
        "RefTimeMs",
        "Iterations",
        "ArgSize",
        "ArgDepth",
        "ArgMeanBranchFactor",
      )
      .forEach(writer::cell)
    writer.newRow()
  }

  private fun printBoundedHeader() {
    printCommonHeader()
    listOf("Iterations").forEach(writer::cell)
    writer.newRow()
  }

  private fun printMddHeader() {
    printCommonHeader()
    listOf("ViolatingSize", "StateSpaceSize", "HitCount", "QueryCount", "CacheSize")
      .forEach(writer::cell)
    writer.newRow()
  }

  private fun printChcHeader() {
    printCommonHeader()
    writer.newRow()
  }

  private fun printSymbolicHeader() {
    listOf(
        "id",
        "modelPath",
        "modelName",
        "stateSpaceSize",
        "finalMddSize",
        "totalTimeUs",
        "ssgTimeUs",
        "nodeCount",
        "unionCacheSize",
        "unionQueryCount",
        "unionHitCount",
      )
      .forEach(writer::cell)
    if (
      iterationStrategy in
        setOf(MddChecker.IterationStrategy.GSAT, MddChecker.IterationStrategy.SAT)
    ) {
      listOf("saturateCacheSize", "saturateQueryCount", "saturateHitCount").forEach(writer::cell)
    }
    listOf("relProdCacheSize", "relProdQueryCount", "relProdHitCount").forEach(writer::cell)
    if (
      iterationStrategy in
        setOf(MddChecker.IterationStrategy.GSAT, MddChecker.IterationStrategy.SAT)
    ) {
      listOf("saturatedNodeCount").forEach(writer::cell)
    }
  }
}
