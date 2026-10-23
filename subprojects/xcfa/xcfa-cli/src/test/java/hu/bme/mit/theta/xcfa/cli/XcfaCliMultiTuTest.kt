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
import org.junit.jupiter.api.Test

class XcfaCliMultiTuTest {

  @Test
  fun testMultiTuParse() {
    main(
      arrayOf(
        "--input-type",
        "C",
        "--input",
        javaClass.getResource("/c/multi_tu/multi-tu-test.yml")!!.path,
        "--backend",
        "NONE",
        "--stacktrace",
        "--debug",
      )
    )
  }
}
