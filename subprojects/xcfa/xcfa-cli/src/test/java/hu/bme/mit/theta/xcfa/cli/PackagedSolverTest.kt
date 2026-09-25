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

import java.io.File
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * A portfolio that names a solver the archive does not ship fails at run time with no useful
 * message, and only on the tasks that reach that branch. Pin both ends here instead.
 */
class PackagedSolverTest {

  private val cliDir =
    File("").absoluteFile.let {
      if (it.name == "xcfa-cli") it else File(it, "subprojects/xcfa/xcfa-cli")
    }
  private val portfolioDir = File(cliDir, "src/main/java/hu/bme/mit/theta/xcfa/cli/portfolio")
  private val versioned = Regex("\"((?:cvc5|mathsat|bitwuzla)):([0-9][0-9.]*)\"")

  /** Solvers packaged into the SV-COMP archive, as declared in build.gradle.kts. */
  private fun packagedSvcomp(): List<String> {
    val build = File(cliDir, "build.gradle.kts").readText()
    val block =
      build.substringAfter("toolName = \"Theta-svcomp\"").substringBefore("readmeTemplate")
    return versioned.findAll(block).map { it.groupValues[1] + ":" + it.groupValues[2] }.toList()
  }

  @Test
  fun `the svcomp archive ships one version per solver family`() {
    val byFamily = packagedSvcomp().groupBy { it.substringBefore(':') }
    byFamily.forEach { (family, versions) ->
      assertEquals(1, versions.size, "$family is packaged as $versions; ship only the latest")
    }
  }

  @Test
  fun `every solver the svcomp portfolios name is packaged`() {
    val packaged = packagedSvcomp().toSet()
    // The CHC portfolios ship in their own archive with their own solver list.
    val svcompPortfolios =
      portfolioDir.listFiles { f -> f.name.endsWith(".kt") && !f.name.startsWith("chccomp") }!!
    val missing = mutableListOf<String>()
    svcompPortfolios.forEach { f ->
      versioned.findAll(f.readText()).forEach {
        val solver = it.groupValues[1] + ":" + it.groupValues[2]
        if (solver !in packaged) missing.add("${f.name}: $solver")
      }
    }
    assertTrue(missing.isEmpty(), "not in the Theta-svcomp archive: $missing")
  }
}
