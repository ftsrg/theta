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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * Copies memory, for the `mem*` functions that no one has defined.
 *
 * Nothing modelled them before: [UnresolvedInvokeToHavocPass] will not take a call whose arguments
 * are pointers, so `memcpy` reached the analysis as a call to a function that does not exist and
 * brought it down ("No such method memcpy"). The copy is spelled out instead, one element at a
 * time; nobody minds that it is long, only that it is right.
 *
 * The count is in **bytes**, but memory is modelled as `arrays[base][index]` over *typed* elements,
 * not bytes -- so the copy is done in the element type the pointer points at, `n / sizeof(element)`
 * of them. That is exact whenever the byte count is a whole number of elements, which is what
 * `memcpy(p, q, sizeof *p)` and `memcpy(buf, src, 100 * sizeof(char))` are.
 *
 * It also means the count has to be *known*. A symbolic one wants a loop, and a loop wants the
 * element size to divide a bound we cannot see -- so it is not attempted, and such a call is left
 * exactly as it was: it will still fail, loudly, which is the same as before and better than a copy
 * that quietly moves the wrong number of bytes. Same for a pointer to a struct, which has no single
 * element type to copy in.
 */
class MemoryFunctionsPass(val parseContext: ParseContext, val uniqueWarningLogger: Logger) :
  ProcedurePass {

  companion object {

    /** `dst`, `src`, `n` -- the copying pair. */
    private val COPY = setOf("memcpy", "memmove", "__builtin_memcpy", "__builtin_memmove")

    /** `dst`, `c`, `n` -- fills with a byte. */
    private val FILL = setOf("memset", "__builtin_memset")
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val defined = builder.parent.getProcedures().map { it.name }.toSet()

    builder.getEdges().toList().forEach { edge ->
      val labels = edge.label.getFlatLabels()
      if (labels.none { it is InvokeLabel && it.name in COPY + FILL && it.name !in defined }) {
        return@forEach
      }
      val rewritten =
        labels.map { label ->
          if (label !is InvokeLabel || label.name in defined) label
          else if (label.name in COPY) copy(label) ?: label
          else if (label.name in FILL) fill(label) ?: label else label
        }
      if (rewritten != labels) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(rewritten)))
      }
    }
    return builder
  }

  /** `memcpy(dst, src, n)`: `dst[i] = src[i]` for every element the n bytes cover. */
  private fun copy(invoke: InvokeLabel): XcfaLabel? {
    // params are [returnValue, dst, src, n]
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val src = invoke.params[2]
    val element = elementOf(dst) ?: elementOf(src) ?: return giveUp(invoke)
    val count = elementCount(invoke.params[3], element) ?: return giveUp(invoke)

    val stmts =
      (0 until count).map { i ->
        val index = indexOf(i, dst)
        MemoryAssignStmt.create(
          deref(dst, index, element),
          cast(deref(src, indexOf(i, src), element), element.smtType),
        )
      }
    return SequenceLabel(
      stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
    )
  }

  /** `memset(dst, c, n)`: every element covered is set to `c`. */
  private fun fill(invoke: InvokeLabel): XcfaLabel? {
    if (invoke.params.size < 4) return null
    val dst = invoke.params[1]
    val value = invoke.params[2]
    val element = elementOf(dst) ?: return giveUp(invoke)
    val count = elementCount(invoke.params[3], element) ?: return giveUp(invoke)

    // `memset` writes a *byte* into every byte. Setting whole elements to it is the same thing only
    // when the element is one byte wide -- or when the byte is zero, which makes every element zero
    // whatever its width. Any other case would be a different program, so it is not claimed.
    val zero = literalValue(value)?.equals(BigInteger.ZERO) == true
    if (!zero && element.width() != 8) return giveUp(invoke)

    val filler =
      if (zero) element.nullValue as Expr<*>
      else CComplexType.getType(value, parseContext).castTo(value)
    val stmts =
      (0 until count).map { i ->
        MemoryAssignStmt.create(deref(dst, indexOf(i, dst), element), cast(filler, element.smtType))
      }
    return SequenceLabel(
      stmts.map { StmtLabel(it, metadata = invoke.metadata) } + returns(invoke, dst)
    )
  }

  /** `mem*` all return their destination; keep that, so `p = memcpy(p, q, n)` still works. */
  private fun returns(invoke: InvokeLabel, dst: Expr<*>): List<XcfaLabel> {
    val ret = (invoke.params[0] as? RefExpr<*>)?.decl as? VarDecl<*> ?: return listOf()
    return listOf(
      AssignStmtLabel(
        cast(ret, ret.type),
        cast(CComplexType.getType(ret.ref, parseContext).castTo(dst), ret.type),
        metadata = invoke.metadata,
      )
    )
  }

  private fun giveUp(invoke: InvokeLabel): XcfaLabel? {
    uniqueWarningLogger.write(
      Logger.Level.INFO,
      "WARNING: ${invoke.name} with a byte count or element type that cannot be stated exactly" +
        " (a symbolic size, or a pointer to a compound); left unmodelled rather than copying the" +
        " wrong number of bytes.\n",
    )
    return null
  }

  /** The type the pointer points at -- scalars only; a struct has no single element to copy. */
  private fun elementOf(pointer: Expr<*>): CComplexType? {
    val embedded =
      when (val type = CComplexType.getType(pointer, parseContext)) {
        is CPointer -> type.embeddedType
        is CArray -> type.embeddedType
        else -> null
      } ?: return null
    return if (embedded is CInteger || embedded is CReal) embedded else null
  }

  /** How many elements `n` bytes are, or null if that is not a whole, known number of them. */
  private fun elementCount(bytes: Expr<*>, element: CComplexType): Int? {
    val n = literalValue(bytes) ?: return null
    val size = BigInteger.valueOf((element.width() / 8).toLong())
    if (size.signum() == 0) return null
    val (count, remainder) = n.divideAndRemainder(size)
    if (remainder.signum() != 0) return null // a partial element: not ours to model
    if (count.signum() < 0 || count > BigInteger.valueOf(MAX_ELEMENTS)) return null
    return count.toInt()
  }

  /**
   * The value of a constant expression. `memcpy(p, q, 2 * sizeof(int))` reaches here as the
   * multiplication it was written as, not as `8`, so it has to be worked out rather than merely
   * looked at.
   */
  private fun literalValue(expr: Expr<*>): BigInteger? =
    when (val e = ExprUtils.simplify(expr)) {
      is IntLitExpr -> e.value
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(e)
      else -> null
    }

  /** The index of the i-th element, in the type the dereference's offset is built at. */
  private fun indexOf(i: Int, pointer: Expr<*>): Expr<*> =
    CComplexType.getUnsignedLong(parseContext).getValue("$i")

  @Suppress("UNCHECKED_CAST")
  private fun deref(pointer: Expr<*>, index: Expr<*>, element: CComplexType): Dereference<*, *, *> {
    val of = Dereference.of(pointer as Expr<Type>, index as Expr<Type>, element.smtType as Type)
    parseContext.metadata.create(of, "cType", element)
    return of
  }
}

/** Enough for any `sizeof` a benchmark copies; past it, a loop would be the honest model. */
private const val MAX_ELEMENTS = 4096L
