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

import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Constrains a read of a *narrow* memory cell to the range its C type can actually hold.
 *
 * A variable is range-constrained where it is havoc'd ([HavocPromotionAndRange]); a memory cell
 * never was. Under **integer** arithmetic a cell is an unbounded `Int`, so an *unwritten* one reads
 * back as any integer whatsoever -- not merely any `unsigned char`. That is unsound in the
 * direction that produces false alarms, and it produced them:
 * ```
 * unsigned char *a = alloca(2);
 * int r = (int) a[0] - (int) a[1];   // really in [-255, 255]
 * return -r;                         // reported as a signed overflow
 * ```
 *
 * Four probes pinned it exactly -- uninitialised cells → Unsafe; the same cells written first →
 * Safe; the same arithmetic through plain variables → Safe; the uninitialised version under
 * `--arithmetic bitvector` → Safe. Under bitvector the cell's SMT type is already the narrow one,
 * and a written cell carries the cast its write applied, so **only an unwritten cell under integer
 * arithmetic** misbehaves. It explains five known no-overflow false alarms at once, among them
 * `termination-memory-alloca/openbsd_cstrncmp-alloca-1` (one of run 84's three genuine
 * regressions), the `openbsd_cstrcmp-alloca-*` pair and `dirname-1`.
 *
 * Stated as an `assume` rather than a cast on the read. `CComplexType.castTo` would be a **no-op
 * for signed** narrow types -- `signedCast` returns the operand untouched unless
 * `--enable-signed-wraparound` is set, because signed overflow is undefined before C23 -- so it
 * would fix `unsigned char` and silently miss `char`. `limit()` states `MIN <= e <= MAX` directly
 * and is exact for both.
 *
 * Only types *narrower* than `int` are constrained. An `int`-and-wider cell has the same gap in
 * principle, but it did not show up as a false alarm (two arbitrary `int`s genuinely can overflow
 * when added, so nothing is provable there anyway) and constraining every read of every cell would
 * cost far more than it buys.
 */
class NarrowCellRangePass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (edge in ArrayList(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      if (labels.none { it is StmtLabel && narrowReadsOf(it.stmt).isNotEmpty() }) continue
      val rewritten =
        labels.flatMap { label ->
          if (label !is StmtLabel) listOf(label)
          else {
            val reads = narrowReadsOf(label.stmt)
            // One assume per read, immediately before the statement that performs it: the cell's
            // value cannot have changed in between, and a cell written earlier on this same edge
            // was written through a cast, so constraining the pre-state is sound either way.
            reads.map { StmtLabel(limitOf(it), metadata = label.metadata) } + label
          }
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(rewritten, edge.label.metadata)))
    }
    return builder
  }

  private fun limitOf(deref: Expr<*>): AssumeStmt =
    CComplexType.getType(deref, parseContext).limit(deref)

  /** The narrow-typed cell reads a statement performs, in evaluation order, without duplicates. */
  private fun narrowReadsOf(stmt: hu.bme.mit.theta.core.stmt.Stmt): List<Expr<*>> {
    val out = LinkedHashSet<Expr<*>>()
    when (stmt) {
      // The target of a memory write is an lvalue, not a read -- but the *address* it is computed
      // from is evaluated, and may itself dereference memory.
      is MemoryAssignStmt<*, *, *> -> {
        (stmt.deref as Dereference<*, *, *>).let {
          collect(it.array, out)
          collect(it.offset, out)
        }
        collect(stmt.expr, out)
      }

      is AssignStmt<*> -> collect(stmt.expr, out)
      is AssumeStmt -> collect(stmt.cond, out)
      is SequenceStmt -> stmt.stmts.forEach { out.addAll(narrowReadsOf(it)) }
      else -> {}
    }
    return out.toList()
  }

  private fun collect(expr: Expr<*>, out: MutableSet<Expr<*>>) {
    if (expr is Dereference<*, *, *>) {
      collect(expr.array, out)
      collect(expr.offset, out)
      if (isNarrowCell(expr)) out.add(expr)
      return
    }
    expr.ops.forEach { collect(it, out) }
  }

  /**
   * Whether this cell read needs constraining: an integer C type narrower than `int`, held in an
   * unbounded `Int`. Under bitvector arithmetic the SMT type is already the narrow one and there is
   * nothing to state; a cell whose C type was lost to a rebuild falls back to `int` and is skipped,
   * which only ever means constraining less.
   */
  private fun isNarrowCell(deref: Dereference<*, *, *>): Boolean {
    if (deref.type !is IntType) return false
    val type = CComplexType.getType(deref, parseContext)
    if (type !is CInteger) return false
    return type.width() < CComplexType.getSignedInt(parseContext).width()
  }
}
