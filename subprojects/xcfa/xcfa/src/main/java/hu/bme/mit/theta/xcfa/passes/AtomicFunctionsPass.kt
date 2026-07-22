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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.AtomicBeginLabel
import hu.bme.mit.theta.xcfa.model.AtomicEndLabel
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

/**
 * Lowers the GCC `__atomic_*` builtins and their C11 `<stdatomic.h>` `atomic_*` spellings into
 * memory operations wrapped in an atomic block, so that a read-modify-write cannot be interleaved.
 * The frontend cannot express these type-generic macros in the grammar, so it emits them as ordinary
 * calls ([InvokeLabel]s, `params[0]` the return variable, `params[1..]` the arguments) and this pass
 * — running in the same group as [CLibraryFunctionsPass], before [UnresolvedInvokeToHavocPass] —
 * turns each into its statement sequence between an [AtomicBeginLabel] and an [AtomicEndLabel].
 *
 * Memory orders are ignored: the analysis is sequentially consistent, so a fence and any ordering
 * constraint hold vacuously. A pointer argument is used as an expression (not restricted to a base
 * variable like `CLibraryFunctionsPass.getParam`), so `__atomic_load_n(&a[i], …)` and `&s.f` work.
 */
class AtomicFunctionsPass(val parseContext: ParseContext) : ProcedurePass {

  private var casCounter = 0

  private enum class BitOp {
    ADD,
    SUB,
    OR,
    AND,
    XOR,
    NAND,
  }

  private val loadNames = setOf("__atomic_load_n", "__atomic_load", "atomic_load", "atomic_load_explicit")
  private val storeNames =
    setOf("__atomic_store_n", "__atomic_store", "atomic_store", "atomic_store_explicit", "atomic_init")
  private val exchangeNames =
    setOf("__atomic_exchange_n", "__atomic_exchange", "atomic_exchange", "atomic_exchange_explicit")
  // desired is a *value* for these; `__atomic_compare_exchange` (no `_n`) takes a *pointer* to it.
  private val casValueNames =
    setOf(
      "__atomic_compare_exchange_n",
      "atomic_compare_exchange_strong",
      "atomic_compare_exchange_weak",
      "atomic_compare_exchange_strong_explicit",
      "atomic_compare_exchange_weak_explicit",
    )
  private val casPtrNames = setOf("__atomic_compare_exchange")
  // fetch_op: return the old value. op_fetch: return the new value.
  private val fetchOldOps =
    mapOf(
      "__atomic_fetch_add" to BitOp.ADD,
      "__atomic_fetch_sub" to BitOp.SUB,
      "__atomic_fetch_or" to BitOp.OR,
      "__atomic_fetch_and" to BitOp.AND,
      "__atomic_fetch_xor" to BitOp.XOR,
      "__atomic_fetch_nand" to BitOp.NAND,
      "atomic_fetch_add" to BitOp.ADD,
      "atomic_fetch_sub" to BitOp.SUB,
      "atomic_fetch_or" to BitOp.OR,
      "atomic_fetch_and" to BitOp.AND,
      "atomic_fetch_xor" to BitOp.XOR,
      "atomic_fetch_add_explicit" to BitOp.ADD,
      "atomic_fetch_sub_explicit" to BitOp.SUB,
      "atomic_fetch_or_explicit" to BitOp.OR,
      "atomic_fetch_and_explicit" to BitOp.AND,
      "atomic_fetch_xor_explicit" to BitOp.XOR,
    )
  private val opFetchNew =
    mapOf(
      "__atomic_add_fetch" to BitOp.ADD,
      "__atomic_sub_fetch" to BitOp.SUB,
      "__atomic_or_fetch" to BitOp.OR,
      "__atomic_and_fetch" to BitOp.AND,
      "__atomic_xor_fetch" to BitOp.XOR,
      "__atomic_nand_fetch" to BitOp.NAND,
    )
  // Fences: a no-op under sequential consistency (nothing may be reordered around them anyway).
  private val fenceNames =
    setOf(
      "__atomic_thread_fence",
      "__atomic_signal_fence",
      "atomic_thread_fence",
      "atomic_signal_fence",
      "atomic_fence",
      "atomic_fence_rlx",
      "atomic_fence_rel",
      "atomic_fence_acq",
      "atomic_fence_acq_rel",
      "atomic_fence_seq_cst",
    )

  private fun handled(name: String) =
    name in loadNames ||
      name in storeNames ||
      name in exchangeNames ||
      name in casValueNames ||
      name in casPtrNames ||
      name in fetchOldOps ||
      name in opFetchNew ||
      name in fenceNames

  private fun predicate(label: XcfaLabel): Boolean = label is InvokeLabel && handled(label.name)

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    for (edge in ArrayList(builder.getEdges())) {
      val edges = edge.splitIf(this::predicate)
      if (
        edges.size > 1 ||
          (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))
      ) {
        builder.removeEdge(edge)
        edges.forEach {
          val first = (it.label as SequenceLabel).labels[0]
          if (predicate(first)) {
            val invoke = first as InvokeLabel
            val labels = lower(invoke, builder)
            builder.addEdge(XcfaEdge(it.source, it.target, SequenceLabel(labels), it.label.metadata))
          } else {
            builder.addEdge(it.withLabel(SequenceLabel(it.label.labels)))
          }
        }
      }
    }
    return builder
  }

  /** The C type the pointer argument points at, i.e. the type of the cell the operation touches. */
  private fun pointeeOf(ptr: Expr<*>): CComplexType =
    when (val t = CComplexType.getType(ptr, parseContext)) {
      is CPointer -> t.embeddedType
      is CArray -> t.embeddedType
      else ->
        throw UnsupportedFrontendElementException(
          "Atomic operation on a non-pointer argument of type $t"
        )
    }

  /** `*ptr` as a [Dereference] of the pointee type at offset 0. */
  private fun deref(ptr: Expr<*>, pointee: CComplexType): Dereference<*, *, *> {
    val offset = CComplexType.getSignedLong(parseContext).nullValue
    return Dereference(cast(ptr, ptr.type), cast(offset, ptr.type), pointee.smtType)
  }

  @Suppress("UNCHECKED_CAST")
  private fun bitwise(op: BitOp, old: Expr<*>, operand: Expr<*>, pointee: CComplexType): Expr<*> {
    val a = pointee.castTo(old)
    val b = pointee.castTo(operand)
    return when (op) {
      BitOp.ADD -> Add(a, b)
      BitOp.SUB -> Sub(a, b)
      BitOp.OR,
      BitOp.AND,
      BitOp.XOR,
      BitOp.NAND -> {
        if (pointee.smtType !is BvType)
          throw UnsupportedFrontendElementException(
            "Atomic bitwise fetch needs bitvector arithmetic, got ${pointee.smtType}"
          )
        val x = cast(a, pointee.smtType) as Expr<BvType>
        val y = cast(b, pointee.smtType) as Expr<BvType>
        when (op) {
          BitOp.OR -> BvExprs.Or(listOf(x, y))
          BitOp.AND -> BvExprs.And(listOf(x, y))
          BitOp.XOR -> BvExprs.Xor(listOf(x, y))
          else -> BvExprs.Not(BvExprs.And(listOf(x, y))) // NAND
        }
      }
    }
  }

  /**
   * Wraps a read-modify-write's statements in an atomic block. The block is what marks the accesses
   * atomic for the multi-threaded race detector (which tracks atomicity by the begin/end fences) and
   * keeps them uninterleavable. In a single-threaded program there is nothing to interleave and no
   * race to detect, so the fences are pure redundancy — and worse, the single-thread monolithic
   * adapter rejects any label that is not a plain statement; the whole edge is one atomic transition
   * there anyway, so emit the bare statements. `multiThreading` is set at parse time on any `pthread`
   * call, before this pass runs.
   */
  private fun atomic(body: List<XcfaLabel>): List<XcfaLabel> =
    if (parseContext.multiThreading) listOf(AtomicBeginLabel()) + body + listOf(AtomicEndLabel())
    else body

  private fun lower(invoke: InvokeLabel, builder: XcfaProcedureBuilder): List<XcfaLabel> {
    val name = invoke.name
    val ret = invoke.params[0] // params[0] is the (possibly unused, for void ops) return variable
    val args = invoke.params.drop(1)

    if (name in fenceNames) return listOf(NopLabel)

    if (name in loadNames) {
      // ret = *p  -- a single memory read, already atomic; the block keeps it uniform.
      val p = args[0]
      return atomic(listOf(AssignStmtLabel(ret, deref(p, pointeeOf(p)))))
    }

    if (name in storeNames) {
      // *p = v ; void.  __atomic_store(p, &v, order) passes v by pointer, __atomic_store_n by value.
      val p = args[0]
      val pointee = pointeeOf(p)
      val value = if (name == "__atomic_store") deref(args[1], pointeeOf(args[1])) else args[1]
      return atomic(listOf(AssignStmtLabel(deref(p, pointee), pointee.castTo(value))))
    }

    if (name in exchangeNames) {
      // ret = *p ; *p = v.  __atomic_exchange (no _n) passes v and ret by pointer.
      val p = args[0]
      val pointee = pointeeOf(p)
      return if (name == "__atomic_exchange") {
        // __atomic_exchange(p, val_ptr, ret_ptr, order): *ret_ptr = *p ; *p = *val_ptr
        val valPtr = args[1]
        val retPtr = args[2]
        atomic(
          listOf(
            AssignStmtLabel(deref(retPtr, pointeeOf(retPtr)), deref(p, pointee)),
            AssignStmtLabel(deref(p, pointee), pointee.castTo(deref(valPtr, pointeeOf(valPtr)))),
          )
        )
      } else {
        atomic(
          listOf(
            AssignStmtLabel(ret, deref(p, pointee)),
            AssignStmtLabel(deref(p, pointee), pointee.castTo(args[1])),
          )
        )
      }
    }

    fetchOldOps[name]?.let { op ->
      // old = *p ; *p = old <op> v ; ret = old.  ret carries the old value.
      val p = args[0]
      val pointee = pointeeOf(p)
      return atomic(
        listOf(
          AssignStmtLabel(ret, deref(p, pointee)),
          AssignStmtLabel(deref(p, pointee), pointee.castTo(bitwise(op, ret, args[1], pointee))),
        )
      )
    }

    opFetchNew[name]?.let { op ->
      // *p = *p <op> v ; ret = the new value.
      val p = args[0]
      val pointee = pointeeOf(p)
      val newValue = pointee.castTo(bitwise(op, deref(p, pointee), args[1], pointee))
      return atomic(
        listOf(
          AssignStmtLabel(deref(p, pointee), newValue),
          AssignStmtLabel(ret, deref(p, pointee)),
        )
      )
    }

    if (name in casValueNames || name in casPtrNames) {
      return lowerCas(invoke, builder, name in casValueNames)
    }

    error("AtomicFunctionsPass: unhandled atomic builtin $name")
  }

  /**
   * `compare_exchange(p, expected, desired, …)`: if `*p == *expected`, store `desired` into `*p` and
   * return true; otherwise load `*p` into `*expected` and return false. Modelled branch-free inside
   * one atomic block with [Ite]s so it stays a straight-line label sequence. The current values are
   * captured into temporaries *first*, so the two stores below cannot re-read a cell one of them has
   * already changed (and it stays correct even if `p` and `expected` alias):
   * ```
   *   old = *p ; exp = *expected
   *   *p        = old == exp ? desired : old
   *   *expected = old == exp ? exp     : old      (write the current value back on failure)
   *   ret       = old == exp ? 1       : 0
   * ```
   */
  @Suppress("UNCHECKED_CAST")
  private fun lowerCas(
    invoke: InvokeLabel,
    builder: XcfaProcedureBuilder,
    desiredIsValue: Boolean,
  ): List<XcfaLabel> {
    val ret = invoke.params[0]
    val args = invoke.params.drop(1)
    val p = args[0]
    val expectedPtr = args[1]
    val pointee = pointeeOf(p)
    val expPointee = pointeeOf(expectedPtr)

    val oldVar = Decls.Var("__theta_atomic_cas_old_${casCounter++}", pointee.smtType)
    val expVar = Decls.Var("__theta_atomic_cas_exp_${casCounter++}", expPointee.smtType)
    builder.addVar(oldVar)
    builder.addVar(expVar)
    val old: Expr<*> = oldVar.ref
    val exp: Expr<*> = expVar.ref

    val desired = if (desiredIsValue) args[2] else deref(args[2], pointeeOf(args[2]))
    val success =
      cast(Eq(cast(old, pointee.smtType), cast(exp, pointee.smtType)), BoolType.getInstance())

    val newAtP = Ite(success, cast(pointee.castTo(desired), pointee.smtType), cast(old, pointee.smtType))
    val newAtExpected = Ite(success, cast(exp, expPointee.smtType), cast(old, expPointee.smtType))
    val retType = CComplexType.getType(ret, parseContext)
    val retSuccess =
      Ite(
        success,
        cast(retType.unitValue, retType.smtType),
        cast(retType.nullValue, retType.smtType),
      )

    return atomic(
      listOf(
        AssignStmtLabel(oldVar, deref(p, pointee)),
        AssignStmtLabel(expVar, deref(expectedPtr, expPointee)),
        AssignStmtLabel(deref(p, pointee), pointee.castTo(newAtP)),
        AssignStmtLabel(deref(expectedPtr, expPointee), expPointee.castTo(newAtExpected)),
        AssignStmtLabel(ret, retSuccess),
      )
    )
  }
}
