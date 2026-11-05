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
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.DivExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.MemoryModelType
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * Under the cell-per-value models an access indexes a block in cells, one per scalar element, so
 * memsafety must record a heap block's size in cells too, not in the bytes the program asks for. A
 * block whose element type is not known is refused and rebuilt under bytes.
 */
class HeapBoundCellsTest {

  private fun sizes(
    program: String,
    architecture: ArchitectureType = ArchitectureType.ILP32,
    memoryModel: MemoryModelType = MemoryModelType.multi,
  ): List<Expr<*>> {
    val parseContext = ParseContext()
    parseContext.architecture = architecture
    parseContext.arithmetic = ArithmeticType.integer
    parseContext.memoryModel = memoryModel
    parseContext.isCheckMemsafety = true
    val (xcfa, _, _) =
      getXcfaFromC(
        javaClass.getResourceAsStream("/heap-bounds/$program")!!,
        parseContext,
        false,
        XcfaProperty(ErrorDetection.MEMSAFETY),
        NullLogger.getInstance(),
      )
    val stmts =
      xcfa.procedures
        .flatMap { it.edges }
        .flatMap { it.getFlatLabels() }
        .mapNotNull { (it as? StmtLabel)?.stmt }
    val writes =
      stmts
        .filterIsInstance<AssignStmt<*>>()
        .filter { it.varDecl.name == "__theta_ptr_size" }
        .flatMap { sizesIn(it.expr) }
    // A size the simplifier propagated is left in the bound check `size <= offset`.
    val checked = stmts.filterIsInstance<AssumeStmt>().flatMap { boundsIn(it.cond) }
    return writes + checked
  }

  private fun boundsIn(expr: Expr<*>): List<Expr<*>> =
    (if (expr is LeqExpr<*>) listOf(expr.leftOp) else listOf()) + expr.ops.flatMap(::boundsIn)

  /**
   * The sizes written by [expr]: a write, or the array literal the simplifier folds writes into.
   */
  private fun sizesIn(expr: Expr<*>): List<Expr<*>> =
    when (expr) {
      is ArrayWriteExpr<*, *> -> sizesIn(expr.array) + expr.elem
      is ArrayLitExpr<*, *> -> expr.elements.map { it.get2() }
      else -> listOf()
    }

  private fun List<Expr<*>>.literals(): Set<BigInteger> =
    mapNotNull { (it as? IntLitExpr)?.value }.toSet()

  private fun assertCells(sizes: List<Expr<*>>, cells: Int, bytes: Int) {
    assertTrue(cells.toBigInteger() in sizes.literals(), "expected $cells cells in $sizes")
    assertFalse(bytes.toBigInteger() in sizes.literals(), "the byte count $bytes in $sizes")
  }

  @Test
  fun intBlockIsBoundedInCells() {
    val sizes = sizes("int-block.c")
    assertCells(sizes, 4, 16)
  }

  @Test
  fun longBlockUnderLp64() {
    val sizes = sizes("long-block.c", ArchitectureType.LP64)
    assertCells(sizes, 1, 8)
  }

  @Test
  fun structArrayIsBoundedByElementCells() {
    val sizes = sizes("struct-array.c", ArchitectureType.LP64)
    assertCells(sizes, 9, 39)
  }

  @Test
  fun wrapperTakesTheCallersElementType() {
    for (model in listOf(MemoryModelType.multi, MemoryModelType.flat)) {
      val sizes = sizes("void-wrapper.c", memoryModel = model)
      assertFalse(16.toBigInteger() in sizes.literals(), "the byte count under $model in $sizes")
      assertTrue(
        4.toBigInteger() in sizes.literals() || sizes.any { it is DivExpr<*> },
        "expected the cells of an int block under $model in $sizes",
      )
    }
  }

  @Test
  fun blockWithoutElementTypeIsRefused() {
    assertThrows<RequiresByteAddressedMemoryException> { sizes("untyped-block.c") }
  }

  @Test
  fun blockSmallerThanAnElementIsRefused() {
    assertThrows<RequiresByteAddressedMemoryException> { sizes("sub-element-block.c") }
  }
}
