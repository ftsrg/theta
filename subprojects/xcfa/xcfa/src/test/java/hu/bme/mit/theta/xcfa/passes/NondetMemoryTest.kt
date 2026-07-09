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

import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Regression test: __VERIFIER_nondet_memory(ptr, size) used to be silently turned into a havoc of
 * the unused return-value slot, dropping the effect on the pointed-to memory entirely (vacuous
 * "safe" results). Nondet calls with real arguments must fail loudly instead.
 */
class NondetMemoryTest {

  private fun runPasses(input: XcfaProcedureBuilderContext.() -> Unit): XcfaProcedureBuilder {
    val builder = XcfaBuilder("")
    val procedureBuilder = builder.procedure("", input).builder
    return listOf(NormalizePass(), DeterministicPass(), NondetFunctionPass()).fold(
      procedureBuilder
    ) { acc, pass ->
      pass.run(acc)
    }
  }

  @Test
  fun nondetWithArgumentsIsRejected() {
    assertThrows(IllegalStateException::class.java) {
      runPasses {
        "ret" type Int()
        "ptr" type Int()
        "sz" type Int()
        (init to "L1") { "__VERIFIER_nondet_memory"("ret", "ptr", "sz") }
      }
    }
  }

  @Test
  fun nondetReturnValueStillHavoced() {
    val result = runPasses {
      "x" type Int()
      (init to "L1") { "__VERIFIER_nondet_int"("x") }
    }
    val labels = result.getEdges().flatMap { (it.label as SequenceLabel).labels }
    assertTrue(labels.any { it is StmtLabel && it.stmt is HavocStmt<*> })
    assertTrue(labels.none { it is InvokeLabel })
  }
}
