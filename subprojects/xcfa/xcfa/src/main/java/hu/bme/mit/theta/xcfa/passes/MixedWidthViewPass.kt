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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.declaration.FunctionIds
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intValue
import java.util.Collections
import java.util.WeakHashMap

/**
 * Refuses a program that reads or writes one object through scalars of different widths, because
 * `multi` and `flat` give each scalar one cell: a write through a `char *` and a read of the `long`
 * it overlaps never meet, so both a Safe and an Unsafe answer can be wrong. Under `bytes` every
 * object is its bytes, so the frontend retries there on [RequiresByteAddressedMemoryException].
 *
 * The check needs the C types, so it runs on the whole model before [ReferenceElimination] folds
 * the addresses away. Pointers are grouped by what flows between them: assignments, call arguments
 * and returns. It is insensitive to control flow and to the offset, so it may refuse a program that
 * never mixes widths at run time, but it only compares pointers that are dereferenced, which leaves
 * `container_of`-style casts alone.
 *
 * A pointer stored in memory is tracked by the pointee layout of the cell that holds it, so that
 * `h.buf = (char *)&x; h.buf[1] = 1;` is found, while an `int *` and a `char *` field stay apart. A
 * struct is compared by the widths of its scalars, and the address of a member (`&s.i`) only by the
 * member's own, as a `char` and an `int` member of a struct do not make its fields mixed views.
 */
class MixedWidthViewPass(private val parseContext: ParseContext) : ProcedurePass {

  private companion object {
    // Every procedure builder has its own pass instance, and one check covers the whole model.
    val checked: MutableSet<XcfaBuilder> = Collections.newSetFromMap(WeakHashMap())
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (parseContext.memoryModel.byteAddressed()) return builder
    if (!synchronized(checked) { checked.add(builder.parent) }) return builder
    Views(builder.parent.getProcedures()).mixedWidths()?.let { widths ->
      throw RequiresByteAddressedMemoryException(
        "One object is accessed through scalars of different widths ($widths bytes), which the" +
          " cell-per-value memory models cannot relate."
      )
    }
    return builder
  }

  /** The cell of a stored pointer, named by the widths of the scalars it points to. */
  private data class StoredPointer(val pointeeWidths: Set<Int>)

  private inner class Views(private val procedures: Set<XcfaProcedureBuilder>) {
    private val unionFind = HashMap<Any, Any>()
    private val scalarViews = LinkedHashMap<Any, MutableSet<Int>>()
    private val layouts = LinkedHashMap<Any, MutableSet<Int>>()
    private val addressHolders = HashSet<VarDecl<*>>()
    private val labels: List<XcfaLabel> =
      procedures.flatMap { procedure -> procedure.getEdges().flatMap { it.getFlatLabels() } }
    private val pointerWidth = CPointer(null, null, parseContext).width()

    fun mixedWidths(): Set<Int>? {
      findAddressHolders()
      labels.forEach(::linkFlows)
      labels.flatMap { it.dereferences }.forEach(::recordAccess)
      val views = HashMap<Any, MutableSet<Int>>()
      scalarViews.forEach { (node, widths) -> views.getOrPut(find(node)) { HashSet() } += widths }
      val others = HashMap<Any, MutableSet<Int>>()
      layouts.forEach { (node, widths) -> others.getOrPut(find(node)) { HashSet() } += widths }
      return views.firstNotNullOfOrNull { (root, widths) ->
        (widths + others[root].orEmpty()).takeIf { it.size > 1 }
      }
    }

    /**
     * An integer as wide as a pointer can carry an address, if a pointer is ever assigned to it.
     */
    private fun findAddressHolders() {
      val assignments = labels.mapNotNull { (it as? StmtLabel)?.stmt as? AssignStmt<*> }
      do {
        val found = addressHolders.size
        assignments
          .filter { cTypeOf(it.varDecl.ref)?.width() == pointerWidth && !isTracked(it.varDecl) }
          .filter { sources(it.expr).isNotEmpty() }
          .forEach { addressHolders += it.varDecl }
      } while (addressHolders.size != found)
    }

    private fun linkFlows(label: XcfaLabel) {
      when (label) {
        is StmtLabel ->
          when (val stmt = label.stmt) {
            is AssignStmt<*> -> if (isTracked(stmt.varDecl)) link(stmt.varDecl, stmt.expr)
            is MemoryAssignStmt<*, *, *> -> linkStore(stmt)
            else -> {}
          }
        is InvokeLabel ->
          when {
            label.name == FunctionPointerCallsPass.INDIRECT_CALL -> linkIndirectCall(label)
            else ->
              procedures.find { it.name == label.name }?.let { linkCall(it, label.params) }
                ?: linkUnknownCall(label)
          }
        is StartLabel ->
          procedures.find { it.name == label.name }?.let { linkCall(it, label.params) }
        else -> {}
      }
    }

    private fun linkStore(stmt: MemoryAssignStmt<*, *, *>) {
      val sources = sources(stmt.expr)
      if (sources.isEmpty()) return
      val declared = declaredCellType(stmt.deref)?.takeIf { pointeeOf(it) != null }
      val cell = storedPointer(declared ?: cTypeOf(stmt.expr))
      sources.forEach { union(cell, it) }
    }

    /**
     * The declared type of the cell [access] names, or null if a non-constant offset hides it or
     * the cell is a union's, which has no single type. The `cType` of a written or address-taken
     * dereference does not say this: it follows the base.
     */
    private fun declaredCellType(access: Dereference<*, *, *>): CComplexType? {
      val base = cTypeOf(access.array)
      val container = if (base is CStruct) base else pointeeOf(base)
      if (container !is CStruct) return container
      if (container.isUnion) return null
      val index = (ExprUtils.simplify(access.offset) as? LitExpr<*>)?.intValue?.toInt()
      return index?.let { cellTypeAt(container, it) }
    }

    private fun linkCall(procedure: XcfaProcedureBuilder, arguments: List<Expr<*>>) {
      procedure.getParams().forEachIndexed { i, (param, _) ->
        arguments.getOrNull(i)?.let { if (isTracked(param)) link(param, it) }
      }
    }

    /** The arguments of an indirect call follow the return value and the function pointer. */
    private fun linkIndirectCall(label: InvokeLabel) {
      val arguments = label.params.take(1) + label.params.drop(2)
      val addressTaken = FunctionIds.getAll().keys
      procedures
        .filter { it.name in addressTaken && it.getParams().size == arguments.size }
        .forEach { linkCall(it, arguments) }
    }

    /** A library function may return a pointer it was given, like `realloc` or `memcpy`. */
    private fun linkUnknownCall(label: InvokeLabel) {
      val returned = label.params.firstOrNull() ?: return
      if (cTypeOf(returned) !is CPointer) return
      val targets = sources(returned)
      val arguments = label.params.drop(1).filter { pointeeOf(cTypeOf(it)) != null }
      for (target in targets) arguments.flatMap { sources(it) }.forEach { union(target, it) }
    }

    private fun link(target: VarDecl<*>, value: Expr<*>) =
      sources(value).forEach { union(target, it) }

    private fun recordAccess(access: Dereference<*, *, *>) {
      val pointee = pointeeOf(cTypeOf(access.array)) ?: return
      for (node in sources(access.array)) {
        if (pointee is CStruct || pointee is CArray) {
          layouts.getOrPut(node) { HashSet() } += scalarWidths(pointee)
        } else if (pointee !is CVoid) {
          scalarViews.getOrPut(node) { HashSet() } += scalarWidths(pointee)
        }
      }
    }

    /** What the address held by [expr] may come from. */
    private fun sources(expr: Expr<*>): Set<Any> =
      when {
        expr.type is BoolType -> emptySet()
        expr is Dereference<*, *, *> ->
          if (pointeeOf(cTypeOf(expr)) != null) setOf(storedPointer(cTypeOf(expr))) else emptySet()
        expr is Reference<*, *> -> addressOf(expr)
        expr is RefExpr<*> -> {
          val variable = expr.decl as? VarDecl<*>
          when {
            variable == null -> emptySet()
            cTypeOf(expr) is CArray -> setOf(objectNode(variable))
            isTracked(variable) -> setOf(variable)
            else -> emptySet()
          }
        }
        expr is IteExpr<*> -> sources(expr.then) + sources(expr.`else`)
        else -> expr.ops.flatMap { sources(it) }.toSet()
      }

    private fun addressOf(reference: Reference<*, *>): Set<Any> {
      val target = reference.expr
      if (target is RefExpr<*> && target.decl is VarDecl<*>) {
        return setOf(objectNode(target.decl as VarDecl<*>))
      }
      val member =
        (target as? Dereference<*, *, *>)?.let(::declaredCellType) ?: pointeeOf(cTypeOf(reference))
      layouts.getOrPut(reference) { HashSet() } += scalarWidths(member)
      return setOf(reference)
    }

    private fun objectNode(variable: VarDecl<*>): Any {
      layouts.getOrPut(variable) { HashSet() } += scalarWidths(cTypeOf(variable.ref))
      return variable
    }

    private fun isTracked(variable: VarDecl<*>) =
      variable in addressHolders || pointeeOf(cTypeOf(variable.ref)) != null

    private fun storedPointer(pointer: CComplexType?) =
      StoredPointer(scalarWidths(pointeeOf(pointer)))

    private fun find(node: Any): Any {
      val parent = unionFind[node] ?: return node
      return find(parent).also { unionFind[node] = it }
    }

    private fun union(a: Any, b: Any) {
      val rootA = find(a)
      val rootB = find(b)
      if (rootA != rootB) unionFind[rootA] = rootB
    }

    private fun pointeeOf(type: CComplexType?): CComplexType? =
      when (type) {
        is CPointer -> if (type.isFunctionPointer) null else type.embeddedType
        is CArray -> type.embeddedType
        else -> null
      }

    private fun scalarWidths(type: CComplexType?): Set<Int> =
      when (type) {
        null,
        is CVoid -> emptySet()
        is CStruct -> type.fields.flatMap { scalarWidths(it.get2()) }.toSet()
        is CArray -> scalarWidths(type.embeddedType)
        else -> setOf((type.width() + 7) / 8)
      }

    private fun cTypeOf(expr: Expr<*>): CComplexType? =
      when (val type = parseContext.metadata.getMetadataValue(expr, "cType").orElse(null)) {
        is CComplexType -> type
        is CSimpleType -> type.actualType
        else -> null
      }
  }
}
