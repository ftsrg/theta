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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.RequiresByteAddressedMemoryException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.ObjectLayout
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Asks for the bytes memory model when a program reads or writes an object byte by byte.
 *
 * Under the multi model a cell holds one *value* of the object, whatever its C width, so a `char`
 * access through `(unsigned char *)&x` names cell `i` of `x`, not byte `i`: after `memset(&x, 0,
 * sizeof x)` on a struct of two pointers, cells 0 and 1 are zero and `((unsigned char *)&x)[5]`
 * reads a cell nothing wrote. Such a program gets no faithful model here, so this pass throws
 * [RequiresByteAddressedMemoryException] and the frontend is rebuilt under `bytes`.
 *
 * It runs after inlining, where the object behind a pointer parameter is visible, and decides from
 * a flow-insensitive closure over pointer copies seeded by the objects' naming variables (`x*`, see
 * [ReferenceElimination]). A one-byte access trips it only where the object's cell at that offset
 * is not one byte wide; an object whose layout or origin is unknown (heap blocks, unions) is left
 * alone, as before this pass.
 */
class ByteViewPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val model = parseContext.memoryModel
    if (model.flatAddressing() || model.byteAddressed()) return builder
    val byteAccesses =
      builder.getEdges().flatMap { edge ->
        edge.getFlatLabels().flatMap { it.dereferences }.filter { isByteAccess(it) }
      }
    if (byteAccesses.isEmpty()) return builder
    val origins = Origins(builder)
    for (access in byteAccesses) {
      for (objectType in origins.objectsOf(access.array)) {
        val widths = cellWidths(objectType) ?: continue
        val offset = (ExprUtils.simplify(access.offset) as? LitExpr<*>)?.let(::literalInt)
        val byteCell =
          if (offset != null) offset in widths.indices && widths[offset] == BYTE
          else widths.all { it == BYTE }
        if (!byteCell) {
          throw RequiresByteAddressedMemoryException(
            "A one-byte access reads or writes a ${objectType.javaClass.simpleName} object byte" +
              " by byte."
          )
        }
      }
    }
    return builder
  }

  /**
   * A one-byte scalar access: a `char` view. Judged by the access's C type, or -- on a copy that
   * unrolling or simplification rebuilt without one -- by the pointee type of its base variable.
   */
  private fun isByteAccess(deref: Dereference<*, *, *>): Boolean {
    val cType =
      parseContext.metadata.getMetadataValue(deref, "cType").orElse(null)
        ?: ((deref.array as? RefExpr<*>)?.decl as? VarDecl<*>)?.let {
          (parseContext.metadata.getMetadataValue(it.ref, "cType").orElse(null) as? CPointer)
            ?.embeddedType
        }
    if (cType is CComplexType) return isScalarInteger(cType) && cType.width() == BYTE
    return (deref.type as? BvType)?.size == BYTE
  }

  /**
   * The width of every cell of an object of [type] under the multi model, in bits; 0 for a cell
   * that holds a sub-object's base. Null when the layout is not known here.
   */
  private fun cellWidths(type: CComplexType): List<Int>? =
    when {
      type is CArray -> {
        val count = ObjectLayout.constantDimension(type)
        val element = cellWidths(type.embeddedType)
        if (count == null || element == null || count * element.size > MAX_CELLS) null
        else List(count) { element }.flatten()
      }
      type is CStruct && type.isUnion -> null
      type is CStruct -> structCellWidths(type)
      isScalarInteger(type) -> listOf(type.width())
      else -> listOf(0)
    }

  private fun structCellWidths(type: CStruct): List<Int>? {
    if (type.unitCount > MAX_CELLS) return null
    val widths = MutableList(type.unitCount) { 0 }
    type.fields
      .groupBy { type.unitOffsetOf(it.get1()) }
      .forEach { (cell, fields) ->
        if (cell !in widths.indices) return null
        val field = fields.singleOrNull()?.get2()
        widths[cell] = if (field != null && isScalarInteger(field)) field.width() else 0
      }
    return widths
  }

  /** `CStruct`, `CArray` and `CPointer` extend `CInteger` too, so they are excluded by name. */
  private fun isScalarInteger(type: CComplexType): Boolean =
    type is CInteger && type !is CPointer && type !is CStruct && type !is CArray

  private fun literalInt(lit: LitExpr<*>): Int? =
    when (lit) {
      is IntLitExpr -> lit.value.toInt()
      is BvLitExpr -> BvUtils.neutralBvLitExprToBigInteger(lit).toInt()
      else -> null
    }

  /** Which objects a base expression may name, from the naming variables and pointer copies. */
  private inner class Origins(builder: XcfaProcedureBuilder) {
    private val literalObjects = mutableMapOf<String, MutableSet<CComplexType>>()
    private val varObjects = mutableMapOf<VarDecl<*>, MutableSet<CComplexType>>()

    init {
      val xcfa = builder.parent
      val assignments =
        (xcfa.getProcedures() + xcfa.getInitProcedures().map { it.first })
          .flatMap { it.getEdges() }
          .flatMap { it.getFlatLabels() }
          .mapNotNull { ((it as? StmtLabel)?.stmt as? AssignStmt<*>) }
      for (global in xcfa.getVars()) {
        val type = namedObjectType(global.wrappedVar) ?: continue
        varObjects.getOrPut(global.wrappedVar) { mutableSetOf() }.add(type)
        global.initValue?.let {
          literalObjects.getOrPut(it.toString()) { mutableSetOf() }.add(type)
        }
      }
      for (assign in assignments) {
        val type = namedObjectType(assign.varDecl) ?: continue
        varObjects.getOrPut(assign.varDecl) { mutableSetOf() }.add(type)
        (ExprUtils.simplify(assign.expr) as? LitExpr<*>)?.let {
          literalObjects.getOrPut(it.toString()) { mutableSetOf() }.add(type)
        }
      }
      do {
        var changed = false
        for (assign in assignments) {
          val sources = objectsOf(assign.expr)
          if (sources.isEmpty()) continue
          changed =
            varObjects.getOrPut(assign.varDecl) { mutableSetOf() }.addAll(sources) || changed
        }
      } while (changed)
    }

    fun objectsOf(base: Expr<*>): Set<CComplexType> =
      when (val e = unbox(base)) {
        is LitExpr<*> -> literalObjects[e.toString()] ?: emptySet()
        is RefExpr<*> -> varObjects[e.decl as? VarDecl<*>] ?: emptySet()
        else ->
          (ExprUtils.simplify(e) as? LitExpr<*>)?.let { literalObjects[it.toString()] }
            ?: emptySet()
      }

    /** The object an `x*` naming variable of [ReferenceElimination] holds the base of. */
    private fun namedObjectType(v: VarDecl<*>): CComplexType? {
      if (!v.name.endsWith("*")) return null
      val pointer = parseContext.metadata.getMetadataValue(v.ref, "cType").orElse(null)
      return (pointer as? CPointer)?.embeddedType
    }

    private fun unbox(e: Expr<*>): Expr<*> =
      when {
        e.ops.size == 1 && e !is Dereference<*, *, *> && e !is RefExpr<*> -> unbox(e.ops[0])
        e is ModExpr<*> -> unbox(e.ops[0])
        else -> e
      }
  }

  private companion object {
    const val BYTE = 8
    const val MAX_CELLS = 1 shl 16
  }
}
