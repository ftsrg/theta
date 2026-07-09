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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Regression: calls to unresolved external functions (e.g. `time`) used to survive into the
 * analysis and crash it with "No such method time." They must instead be havoced.
 */
class UnresolvedInvokeToHavocTest {

  private fun runPasses(input: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilder {
    val builder = XcfaBuilder("")
    val procedureBuilder = builder.procedure("main", input).builder
    return listOf(
        NormalizePass(),
        DeterministicPass(),
        UnresolvedInvokeToHavocPass(NullLogger.getInstance()),
      )
      .fold(procedureBuilder) { acc, pass -> pass.run(acc) }
  }

  @Test
  fun unresolvedCallBecomesHavoc() {
    val result = runPasses {
      "ret" type Int()
      (init to "L1") { "time"("ret", "ret") }
    }
    val labels = result.getEdges().flatMap { (it.label as SequenceLabel).labels }
    assertTrue(labels.none { it is InvokeLabel }, "the unresolved InvokeLabel must be gone")
    assertTrue(labels.any { it is StmtLabel && it.stmt is HavocStmt<*> }, "return value is havoced")
  }
}
