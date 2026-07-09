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
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.xcfa.model.*
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * Calls to unresolved external functions are havoced ONLY when the whole signature is
 * integer-scalar (or literal-null pointers): havocing pointer-writing callees (fscanf!) swallows
 * their side effects and produces vacuously-safe models, and float/pointer returns misrepresent
 * value semantics. Unsafe-to-havoc calls must stay untouched (-> analysis-time error, not a wrong
 * verdict).
 */
class UnresolvedInvokeToHavocTest {

  private fun labelsAfter(
    parseContext: ParseContext,
    input: XcfaProcedureBuilderContext.() -> Unit,
  ): List<XcfaLabel> {
    val builder = XcfaBuilder("")
    val procedureBuilder = builder.procedure("main", input).builder
    val result =
      listOf(
          NormalizePass(),
          DeterministicPass(),
          UnresolvedInvokeToHavocPass(parseContext, NullLogger.getInstance()),
        )
        .fold(procedureBuilder) { acc, pass -> pass.run(acc) }
    return result.getEdges().flatMap { (it.label as SequenceLabel).labels }
  }

  @Test
  fun scalarSignatureIsHavoced() {
    val parseContext = ParseContext()
    lateinit var labels: List<XcfaLabel>
    labels =
      labelsAfter(parseContext) {
        val ret = "ret" type Int()
        parseContext.metadata.create(ret.ref, "cType", CSignedInt(null, parseContext))
        (init to "L1") { "time"("ret") }
      }
    assertTrue(labels.none { it is InvokeLabel }, "scalar-returning call must be havoced")
    assertTrue(labels.any { it is StmtLabel && it.stmt is HavocStmt<*> })
  }

  @Test
  fun nullLiteralPointerArgIsAllowed() {
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        val ret = "ret" type Int()
        parseContext.metadata.create(ret.ref, "cType", CSignedInt(null, parseContext))
        (init to "L1") { "time"("ret", Int(0)) }
      }
    assertTrue(labels.none { it is InvokeLabel }, "time(NULL) must be havoced")
  }

  @Test
  fun pointerArgumentBlocksHavoc() {
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        val ret = "ret" type Int()
        val ptr = "ptr" type Int()
        parseContext.metadata.create(ret.ref, "cType", CSignedInt(null, parseContext))
        parseContext.metadata.create(
          ptr.ref,
          "cType",
          CPointer(null, CSignedInt(null, parseContext), parseContext),
        )
        (init to "L1") { "fscanf"("ret", "ptr") }
      }
    assertTrue(
      labels.any { it is InvokeLabel },
      "pointer-writing call must stay unresolved, not become a silent no-op",
    )
  }

  @Test
  fun missingTypeMetadataBlocksHavoc() {
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        "ret" type Int() // no cType metadata attached
        (init to "L1") { "mystery"("ret") }
      }
    assertTrue(labels.any { it is InvokeLabel }, "unknown-typed call must stay unresolved")
  }

  @Test
  fun controlFlowFunctionsAreNeverHavoced() {
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        val ret = "ret" type Int()
        parseContext.metadata.create(ret.ref, "cType", CSignedInt(null, parseContext))
        (init to "L1") { "_setjmp"("ret") }
      }
    assertTrue(labels.any { it is InvokeLabel }, "setjmp/longjmp must stay unresolved")
  }
}
