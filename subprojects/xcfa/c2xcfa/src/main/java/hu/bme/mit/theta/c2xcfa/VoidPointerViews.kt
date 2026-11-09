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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CChar
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.ReturnLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * Refuses, under the cell memory models, a program that may view one object both through a
 * character pointer and through a pointer to another type. A cell is one member or element whatever
 * its width, so `((char *)v)[i]` on a struct or an `int` reads cell `i`, not byte `i`.
 *
 * The values are followed through `void *` variables, parameters, return values and memory: the
 * `void *` places that may hold the same object are merged flow-insensitively, and a group that is
 * converted from or to both a character pointer and another object pointer, or a direct conversion
 * between the two, throws [RequiresByteAddressedMemoryException], so the program is rebuilt under
 * `bytes`. An integer variable that is assigned an address is a `void *` place too. Pointers punned
 * through unions are not followed.
 */
internal class VoidPointerViews(
  private val parseContext: ParseContext,
  private val builder: XcfaBuilder,
) {

  private enum class View {
    CHAR,
    OTHER,
  }

  /** What a pointer value points at: `void`, or an object seen as one [View]. */
  private sealed interface Target {
    data object Void : Target

    data class Typed(val view: View) : Target
  }

  private val parent = ArrayList<Int>()
  private val views = ArrayList<MutableSet<View>>()
  private val varGroups = LinkedHashMap<VarDecl<*>, Int>()
  private val memory = fresh()
  private val stored = fresh()
  private val procedures = builder.getProcedures().associateBy { it.name }
  private val addressHolders = HashSet<VarDecl<*>>()

  /** Possible callees through a pointer: address-taken functions and those never called by name. */
  private val callbacks: List<XcfaProcedureBuilder> by lazy {
    val called =
      builder
        .getProcedures()
        .flatMap { p -> p.getEdges().flatMap { e -> allLabels(e.label) } }
        .filterIsInstance<InvokeLabel>()
        .map { it.name }
        .toSet()
    val entries = builder.getInitProcedures().map { it.first }.toSet()
    builder.getProcedures().filter {
      it.name in FunctionIds.getAll().keys || (it.name !in called && it !in entries)
    }
  }

  fun check() {
    if (parseContext.memoryModel.byteAddressed()) return
    findAddressHolders()
    builder.getProcedures().forEach { proc ->
      proc.getEdges().forEach { edge -> allLabels(edge.label).forEach(::visit) }
    }
    if (parent.indices.any { views[find(it)].size > 1 }) {
      throw RequiresByteAddressedMemoryException(
        "A void pointer is converted both to or from a character pointer and to or from" +
          " another object pointer, which the cell memory models cannot relate."
      )
    }
  }

  private fun allLabels(label: XcfaLabel): List<XcfaLabel> =
    when (label) {
      is SequenceLabel -> label.labels.flatMap(::allLabels)
      is NondetLabel -> label.labels.flatMap(::allLabels)
      is ReturnLabel -> allLabels(label.enclosedLabel)
      else -> listOf(label)
    }

  private fun visit(label: XcfaLabel) {
    when (label) {
      is StmtLabel ->
        when (val stmt = label.stmt) {
          is AssignStmt<*> -> {
            conversions(stmt.expr)
            assign(stmt.varDecl, stmt.expr)
          }
          is MemoryAssignStmt<*, *, *> -> {
            conversions(stmt.deref)
            conversions(stmt.expr)
            if (target(stmt.deref) == Target.Void || target(stmt.expr) == Target.Void) {
              flowInto(memory, stmt.expr)
            }
          }
          is AssumeStmt -> conversions(stmt.cond)
          else -> {}
        }
      is InvokeLabel -> {
        label.params.forEach(::conversions)
        invoke(label.name, label.params)
      }
      is StartLabel -> {
        label.params.forEach(::conversions)
        procedures[label.name]?.let { bind(it, label.params) }
      }
      else -> {}
    }
  }

  private fun invoke(name: String, params: List<Expr<*>>) {
    val callee = procedures[name]
    when {
      callee != null -> bind(callee, params)
      name == ExpressionVisitor.INDIRECT_CALL -> {
        val actuals = listOf(params[0]) + params.drop(2)
        callbacks
          .filter { it.getParams().size == actuals.size }
          .forEach { bind(it, actuals, exact = false) }
      }
      name in CALLBACK_DATA -> {
        // The data reaches the callback's parameters, and a search returns a pointer into it.
        val group = fresh()
        params.drop(if (name == "pthread_create") 4 else 0).forEach { flowInto(group, it) }
        callbacks.forEach { proc ->
          proc.getParams().forEach { (formal, _) ->
            if (target(formal.ref) == Target.Void) union(varGroup(formal), group)
          }
        }
      }
      name in STORED -> params.forEach { flowInto(stored, it) }
      // These read or write the bytes of all their pointer arguments and return the first one.
      name in BYTEWISE -> fresh().let { group -> params.forEach { flowInto(group, it) } }
      // Any other `void *` result may point into an argument.
      params.isNotEmpty() && target(params[0]) == Target.Void && name !in FRESH ->
        fresh().let { group -> params.forEach { flowInto(group, it) } }
    }
  }

  /**
   * Passes [actuals] to the parameters of [callee], position by position. A call through a pointer
   * is bound to every candidate, so a candidate of another signature is not [exact].
   */
  private fun bind(callee: XcfaProcedureBuilder, actuals: List<Expr<*>>, exact: Boolean = true) {
    callee.getParams().zip(actuals).forEach { (formal, actual) ->
      assign(formal.first, actual, exact)
    }
  }

  /**
   * The integer variables that are assigned an address, directly or through a parameter, so that
   * `(void *)a` after `a = (unsigned long)&x` still reaches `x`.
   */
  private fun findAddressHolders() {
    val labels =
      builder.getProcedures().flatMap { proc -> proc.getEdges().flatMap { allLabels(it.label) } }
    val writes =
      labels.flatMap { label ->
        when (label) {
          is StmtLabel ->
            listOfNotNull((label.stmt as? AssignStmt<*>)?.let { it.varDecl to it.expr })
          is InvokeLabel ->
            procedures[label.name]?.getParams()?.map { it.first }?.zip(label.params).orEmpty()
          else -> emptyList()
        }
      }
    do {
      val found = addressHolders.size
      writes
        .filter { (variable, value) ->
          variable !in addressHolders && isInteger(variable) && addressesIn(value).isNotEmpty()
        }
        .forEach { (variable, _) -> addressHolders += variable }
    } while (addressHolders.size != found)
  }

  private fun isInteger(variable: VarDecl<*>): Boolean {
    val type = parseContext.metadata.getMetadataValue(variable.ref, "cType").orElse(null)
    return type is CInteger &&
      type !is CBool &&
      type !is CPointer &&
      type !is CArray &&
      type !is CStruct
  }

  /** The pointer-valued operands of an integer expression, such as `(unsigned long)&x + 8`. */
  private fun addressesIn(expr: Expr<*>): List<Expr<*>> =
    when {
      expr.type is BoolType || expr is Dereference<*, *, *> -> emptyList()
      target(expr) != null -> listOf(expr)
      else -> expr.ops.flatMap(::addressesIn)
    }

  private fun assign(variable: VarDecl<*>, value: Expr<*>, exact: Boolean = true) {
    when (val to = target(variable.ref)) {
      Target.Void ->
        if (variable in addressHolders) {
          addressesIn(value).forEach { flowInto(varGroup(variable), it) }
        } else {
          flowInto(varGroup(variable), value)
        }
      is Target.Typed -> convert(to, value, exact)
      null -> {}
    }
  }

  /** A [value] used as a pointer to [to]: a view of whatever a `void *` source may hold. */
  private fun convert(to: Target.Typed, value: Expr<*>, exact: Boolean = true) {
    when (val from = target(value)) {
      Target.Void -> add(groupOf(value), to.view)
      is Target.Typed -> if (exact && from.view != to.view) refuseDirect(value)
      null -> {}
    }
  }

  /**
   * Every pointer conversion inside [expr]. A `void *` variable whose address is taken is also
   * written and read through memory.
   */
  private fun conversions(expr: Expr<*>) {
    if (expr is PosExpr<*>) {
      val to = target(expr)
      if (to is Target.Typed) convert(to, expr.op)
    }
    val referenced = (expr as? Reference<*, *>)?.expr as? RefExpr<*>
    if (referenced != null && target(referenced) == Target.Void) {
      union(memory, varGroup(referenced.decl as VarDecl<*>))
    }
    expr.ops.forEach(::conversions)
  }

  /** Records that [value] may be stored in a `void *` place of [group]. */
  private fun flowInto(group: Int, value: Expr<*>) {
    when (val from = target(value)) {
      Target.Void -> union(group, groupOf(value))
      is Target.Typed -> add(group, from.view)
      null -> {}
    }
  }

  /** The group of the `void *` places [value] (a `void *`) may come from. */
  private fun groupOf(value: Expr<*>): Int =
    when (value) {
      is PosExpr<*> ->
        when (target(value.op)) {
          Target.Void -> groupOf(value.op)
          is Target.Typed -> fresh().also { flowInto(it, value.op) }
          null -> fresh()
        }
      is RefExpr<*> -> varGroup(value.decl as VarDecl<*>)
      is Dereference<*, *, *> -> memory
      is IteExpr<*>,
      is AddExpr<*>,
      is SubExpr<*> ->
        fresh().also { group -> value.ops.forEach { if (target(it) != null) flowInto(group, it) } }
      // Any other expression, such as a `?:` the frontend computed as an integer: its addresses.
      else ->
        fresh().also { group -> value.ops.flatMap(::addressesIn).forEach { flowInto(group, it) } }
    }

  private fun target(expr: Expr<*>): Target? {
    if (expr is RefExpr<*> && expr.decl in addressHolders) return Target.Void
    val type =
      parseContext.metadata.getMetadataValue(expr, "cType").orElse(null) as? CComplexType
        ?: return null
    val pointee =
      when (type) {
        is CPointer -> if (type.isFunctionPointer) return null else type.embeddedType
        is CArray -> type.embeddedType
        else -> return null
      }
    return if (pointee == null || pointee is CVoid) Target.Void else Target.Typed(view(pointee))
  }

  private fun view(type: CComplexType): View =
    when {
      type is CChar -> View.CHAR
      type is CArray -> view(type.embeddedType)
      type is CStruct &&
        !type.isUnion &&
        type.fields.isNotEmpty() &&
        type.fields.indices.all {
          type.declaredBitfieldWidth(it) < 0 && view(type.fields[it].get2()) == View.CHAR
        } -> View.CHAR
      else -> View.OTHER
    }

  private fun refuseDirect(value: Expr<*>): Nothing =
    throw RequiresByteAddressedMemoryException(
      "A pointer is converted between a character pointer and another object pointer, which the" +
        " cell memory models cannot relate: ${value.toString().take(200)}"
    )

  private fun varGroup(variable: VarDecl<*>): Int = varGroups.getOrPut(variable) { fresh() }

  private fun fresh(): Int {
    parent.add(parent.size)
    views.add(mutableSetOf())
    return parent.size - 1
  }

  private fun find(x: Int): Int {
    var root = x
    while (parent[root] != root) root = parent[root]
    var node = x
    while (parent[node] != root) {
      val next = parent[node]
      parent[node] = root
      node = next
    }
    return root
  }

  private fun union(a: Int, b: Int) {
    val ra = find(a)
    val rb = find(b)
    if (ra == rb) return
    parent[rb] = ra
    views[ra].addAll(views[rb])
  }

  private fun add(group: Int, view: View) {
    views[find(group)].add(view)
  }

  private companion object {
    /** Functions returning a fresh block or an unrelated pointer. */
    val FRESH =
      setOf(
        "malloc",
        "calloc",
        "valloc",
        "aligned_alloc",
        "memalign",
        "alloca",
        "__builtin_alloca",
        "mmap",
        "__VERIFIER_nondet_pointer",
      )

    val BYTEWISE =
      setOf(
        "memcpy",
        "memmove",
        "mempcpy",
        "memccpy",
        "bcopy",
        "memcmp",
        "bcmp",
        "memset",
        "memchr",
        "memrchr",
        "rawmemchr",
        "realloc",
        "__builtin_memcpy",
        "__builtin_memmove",
        "__builtin_memcmp",
        "__builtin_memset",
      )

    /** Functions that keep a pointer and hand it back later. */
    val STORED = setOf("pthread_setspecific", "pthread_getspecific")

    /** Functions that pass pointer arguments on to a callback. */
    val CALLBACK_DATA =
      setOf("pthread_create", "qsort", "qsort_r", "bsearch", "lfind", "lsearch", "tsearch", "tfind")
  }
}
