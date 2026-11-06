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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

class LocalAddressLifetimeTest {
  companion object {
    @JvmStatic
    fun cases(): List<Array<Any>> =
      listOf(MemoryModelType.multi, MemoryModelType.flat).flatMap { model ->
        listOf(
            arrayOf<Any>(model, "int", "int *p = &local; return *p;", false),
            arrayOf<Any>(
              model,
              "int",
              "__atomic_compare_exchange_n(&g, &local, 1, 0, 5, 5); return local;",
              false,
            ),
            arrayOf<Any>(
              model,
              "int",
              "int *p = &local; { int *q = p; *q = 2; } return local;",
              false,
            ),
            arrayOf<Any>(model, "int *", "int *p = &local; int *q = p; return q;", true),
            arrayOf<Any>(model, "int *", "int *p = &local; return &*p;", true),
            arrayOf<Any>(model, "int", "saved = &local; return local;", true),
            arrayOf<Any>(
              model,
              "int",
              "//scope\n int *p; { int local = 1; p = &local; } return *p;",
              true,
            ),
            arrayOf<Any>(model, "int", "*out = &local; return local;", true),
            arrayOf<Any>(model, "int", "escape(&local); return local;", true),
          )
          .filter { model == MemoryModelType.flat || it[2] != "int *p = &local; return &*p;" }
      }
  }

  @ParameterizedTest
  @MethodSource("cases")
  fun releaseOnlyEscapingAddresses(
    model: MemoryModelType,
    resultType: String,
    body: String,
    escapes: Boolean,
  ) {
    val context = ParseContext()
    context.architecture = ArchitectureType.ILP32
    context.arithmetic = ArithmeticType.integer
    context.memoryModel = model
    context.isCheckMemsafety = true
    val source =
      """
      int g;
      int *saved;
      extern void escape(int *);
      $resultType f(int **out) {
        ${if (body.startsWith("//scope")) "" else "int local = 1;"}
        $body
      }
      int main(void) { int *p; f(&p); return 0; }
      """
        .trimIndent()
    val logger = NullLogger.getInstance()
    val program =
      parseTypeAware(CharStreams.fromString(source)).accept(FunctionVisitor(context, logger))
        as CProgram
    val builder =
      FrontendXcfaBuilder(context, XcfaProperty(ErrorDetection.MEMSAFETY), logger)
        .buildXcfa(program)
    // Inspect lifetime lowering before simplification can propagate the address or drop its writes.
    for (phase in 0..2) builder.getProcedures().forEach { it.optimize(phase) }
    if (body.startsWith("__atomic_compare_exchange_n")) {
      assertTrue(
        builder.getProcedures().flatMap { it.getVars() }.none { it.name.endsWith("local*") },
        "lowered CAS must keep its expected value scalar",
      )
    }
    fun clearsLocal(expr: Expr<*>): Boolean =
      (expr is ArrayWriteExpr<*, *> &&
        expr.index.toString().contains("local*") &&
        (expr.elem as? IntLitExpr)?.value?.signum() == 0) || expr.ops.any(::clearsLocal)
    val reachableEdges = mutableSetOf<XcfaEdge>()
    for (procedure in builder.getProcedures()) {
      val reached = mutableSetOf<XcfaLocation>()
      val pending = ArrayDeque(listOf(procedure.initLoc))
      while (pending.isNotEmpty()) {
        val location = pending.removeFirst()
        if (!reached.add(location)) continue
        location.outgoingEdges.forEach { edge ->
          reachableEdges.add(edge)
          pending.add(edge.target)
        }
      }
    }
    val released =
      reachableEdges
        .flatMap { it.getFlatLabels() }
        .filterIsInstance<StmtLabel>()
        .map { it.stmt }
        .filterIsInstance<AssignStmt<*>>()
        .any { it.varDecl.name == "__theta_ptr_size" && clearsLocal(it.expr) }
    assertEquals(escapes, released, "local address lifetime under $model: $body")
  }
}
