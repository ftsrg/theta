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

import hu.bme.mit.theta.xcfa.cli.XcfaCli.Companion.main
import kotlin.io.path.absolutePathString
import kotlin.io.path.createTempDirectory
import kotlin.io.path.readText
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class XcfaCliTerminationVerifyTest {

  /** A read of an address-taken variable has to see its earlier write when a lasso is checked. */
  @Test
  fun testAsgCegarAddressTakenGuard() {
    val temp = createTempDirectory()
    val params =
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/termination/address_taken_terminates.c")!!.path,
        "--property",
        javaClass.getResource("/c/nontermination/prop/termination.prp")!!.path,
        "--backend",
        "LIVENESS_CEGAR",
        "--domain",
        "PRED_CART",
        "--stacktrace",
        "--debug",
        "--output-directory",
        temp.absolutePathString(),
        "--svcomp",
      )
    main(params)
    val witness = temp.resolve("witness.yml").readText()
    assertTrue("invariant_set" in witness, "Expected a correctness witness, got:\n$witness")
    temp.toFile().deleteRecursively()
  }
}
