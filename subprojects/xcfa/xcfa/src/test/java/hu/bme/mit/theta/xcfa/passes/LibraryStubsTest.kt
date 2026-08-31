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
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

/**
 * What [LibraryStubsPass] may and may not replace.
 *
 * The dangerous direction is silently swallowing an effect: a variadic argument left unwritten, or
 * a call something downstream models properly being flattened into a havoc.
 */
class LibraryStubsTest {

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
          LibraryStubsPass(parseContext, NullLogger.getInstance()),
        )
        .fold(procedureBuilder) { acc, pass -> pass.run(acc) }
    return result.getEdges().flatMap { (it.label as SequenceLabel).labels }
  }

  private fun XcfaProcedureBuilderContext.intVar(parseContext: ParseContext, name: String) =
    (name type Int()).also {
      parseContext.metadata.create(it.ref, "cType", CSignedInt(null, parseContext))
    }

  private fun XcfaProcedureBuilderContext.ptrVar(parseContext: ParseContext, name: String) =
    (name type Int()).also {
      parseContext.metadata.create(
        it.ref,
        "cType",
        CPointer(null, CSignedInt(null, parseContext), parseContext),
      )
    }

  @Test
  fun everyVariadicArgumentIsWritten() {
    // A fixed index set would cover only the first few; the rest would keep their old values while
    // the program believes fscanf filled them.
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        intVar(parseContext, "ret")
        intVar(parseContext, "stream")
        intVar(parseContext, "fmt")
        listOf("a", "b", "c", "d", "e", "f").forEach { ptrVar(parseContext, it) }
        (init to "L1") { "fscanf"("ret", "stream", "fmt", "a", "b", "c", "d", "e", "f") }
      }
    val writes = labels.count { it is StmtLabel && it.stmt is MemoryAssignStmt<*, *, *> }
    assertEquals(6, writes, "all six pointer arguments must be written through")
    assertTrue(labels.none { it is InvokeLabel }, "the call itself must be consumed")
  }

  @Test
  fun flaggedLibraryFunctionIsLeftAlone() {
    // isLibraryFunction means something downstream models this call specifically -- the OC checker
    // supports the thread-specific-key family. Stubbing it to a havoc throws that support away.
    val parseContext = ParseContext()
    val builder = XcfaBuilder("")
    val procedureBuilder =
      builder
        .procedure("main") {
          intVar(parseContext, "ret")
          ptrVar(parseContext, "key")
          (init to "L1") { "pthread_key_create"("ret", "key") }
        }
        .builder
    var result = NormalizePass().run(procedureBuilder)
    result = DeterministicPass().run(result)
    result.getEdges().forEach { e ->
      e.label.getFlatLabels().filterIsInstance<InvokeLabel>().forEach {
        it.isLibraryFunction = true
      }
    }
    result = LibraryStubsPass(parseContext, NullLogger.getInstance()).run(result)
    val labels = result.getEdges().flatMap { it.label.getFlatLabels() }
    assertTrue(
      labels.any { it is InvokeLabel && it.name == "pthread_key_create" },
      "a call flagged isLibraryFunction must survive for its own handler",
    )
  }

  @Test
  fun assumedSuccessReturnsItsFixedValue() {
    // A havoc'd return makes `if (atexit(f)) abort();` reachable in a program where it is not.
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        intVar(parseContext, "ret")
        intVar(parseContext, "handler")
        (init to "L1") { "atexit"("ret", "handler") }
      }
    assertTrue(
      labels.any { it is StmtLabel && it.stmt is AssignStmt<*> },
      "atexit must return its fixed success value",
    )
    assertTrue(
      labels.none { it is StmtLabel && it.stmt is HavocStmt<*> },
      "atexit's return must not be havoced",
    )
  }

  @Test
  fun readOnlyCallOnlyProducesAReturn() {
    val parseContext = ParseContext()
    val labels =
      labelsAfter(parseContext) {
        intVar(parseContext, "ret")
        ptrVar(parseContext, "s")
        (init to "L1") { "strlen"("ret", "s") }
      }
    assertTrue(
      labels.none { it is StmtLabel && it.stmt is MemoryAssignStmt<*, *, *> },
      "strlen only reads; nothing may be written through its argument",
    )
    assertTrue(labels.any { it is StmtLabel && it.stmt is HavocStmt<*> })
  }
}
