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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import java.math.BigInteger
import org.kframework.mpfr.BigFloat

private typealias ArrayType2D = ArrayType<out Type, ArrayType<out Type, out Type>>

/**
 * Converts dereferences to array expressions. The arrays are stored in global variables per type
 * (per combination of array type, offset type, and element type): there is a global array for each
 * such combination. A dereference like (deref array offset) is converted to arrays[array][offset],
 * where arrays is the global array variable corresponding to the types of array, offset, and
 * element. Upon each write to the memory location, the corresponding global array is also updated
 * to reflect the change.
 *
 * There is exactly ONE array per type triple: any per-dereference partition (an earlier version
 * split on a syntactic is-the-base-a-global test) is unsound, because the same cell can be reached
 * both through a global pointer variable and through its constant-folded base literal — the two
 * dereferences would then read and write different arrays, and BMC-style checkers happily pick
 * inconsistent values for them (false counterexamples on ldv-regression, among others). The array
 * starts havoced: stack and heap cells are garbage until written, and globals do not need the
 * array's default value because their zero/explicit initialization is materialized as ordinary
 * writes in the init procedure.
 */
class DereferenceToArrayPass : ProcedurePass {

  companion object {
    /**
     * Start the memory array at zero instead of unconstrained. Unconstrained is the faithful choice,
     * since stack and heap cells hold garbage until written and globals get their zeros from ordinary
     * writes in the init procedure. It is not free for every checker though: a decision-diagram
     * fixpoint enumerates the initial states, and an unconstrained array is not a finite set of them,
     * so the saturation-based checkers need a concrete starting array. Programs that read
     * uninitialized stack or heap then look zeroed, which can hide a bug but cannot invent one.
     */
    var zeroInitialized: Boolean = false
  }

  private lateinit var arraysByType: Map<Triple<Type, Type, Type>, VarDecl<out ArrayType2D>>

  /** Maps a dereference to an identifying type key */
  private fun <A : Type, O : Type, T : Type> Dereference<A, O, T>.getTypeKey():
    Triple<Type, Type, Type> = Triple(array.type, offset.type, type)

  /** Returns an array from the pre-generated lookup of types */
  private fun <A : Type, O : Type, T : Type> Dereference<A, O, T>.getArrays(
    xcfa: XcfaBuilder
  ): VarDecl<ArrayType<A, ArrayType<O, T>>> {
    val arrayType = ArrayType.of(array.type, ArrayType.of(offset.type, type))

    return cast(arraysByType[getTypeKey()]!!, arrayType)
  }

  /** Creates arrays from dereference types */
  private fun createArray(
    key: Triple<Type, Type, Type>,
    xcfa: XcfaBuilder,
  ): VarDecl<out ArrayType2D> {
    val (derefArrayType, derefOffsetType, derefType) = key
    val arrayType = ArrayType.of(derefArrayType, ArrayType.of(derefOffsetType, derefType))

    val decl = Decls.Var("__arrays_${derefArrayType}_${derefOffsetType}_${derefType}", arrayType)
    val zero =
      ArrayLitExpr.of(listOf(), cast(arrayType.elemType.defaultValue, arrayType.elemType), arrayType)
    val globalDecl =
      if (zeroInitialized) XcfaGlobalVar(decl, zero, atomic = true)
      else XcfaGlobalVar(decl, atomic = true)
    val initLabel =
      if (zeroInitialized) AssignStmtLabel(decl, zero) else StmtLabel(HavocStmt.of(decl))
    xcfa.addVar(globalDecl)
    xcfa.getInitProcedures().forEach { (procedure, _) ->
      procedure.initLoc.outgoingEdges.toSet().forEach { edge ->
        procedure.removeEdge(edge)
        procedure.addEdge(edge.withLabel(SequenceLabel(listOf(initLabel, edge.label))))
      }
    }
    return decl as VarDecl<out ArrayType2D>
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    if (!::arraysByType.isInitialized) {
      val arrays = mutableMapOf<Triple<Type, Type, Type>, VarDecl<out ArrayType2D>>()
      val types = mutableSetOf<Triple<Type, Type, Type>>()
      builder.parent.getProcedures().forEach { p ->
        p.getEdges().forEach { e ->
          e.label.dereferences.forEach { deref -> types.add(deref.getTypeKey()) }
        }
      }
      types.forEach { arrays[it] = createArray(it, builder.parent) }
      arraysByType = arrays
    }

    builder.getEdges().toList().forEach { edge ->
      val newLabel = edge.label.replaceDereferences(builder.parent)
      if (newLabel != edge.label) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(newLabel))
      }
    }
    return builder
  }

  private fun XcfaLabel.replaceDereferences(xcfa: XcfaBuilder): XcfaLabel {
    return when (this) {
      is SequenceLabel -> SequenceLabel(labels.map { it.replaceDereferences(xcfa) })
      is NondetLabel -> NondetLabel(labels.map { it.replaceDereferences(xcfa) }.toSet())
      is StmtLabel -> {
        StmtLabel(
          when (stmt) {
            is MemoryAssignStmt<*, *, *> -> {
              // (deref array offset) := expr  -> arrays[array][offset] := expr
              // -> Assign(
              //      arrays,
              //      ArrayWrite(arrays, array, ArrayWrite(ArrayRead(arrays, array), offset, expr))
              //    )
              val deref = stmt.deref
              val arrayType =
                ArrayType.of(deref.array.type, ArrayType.of(deref.offset.type, deref.type))
              val arrays = deref.getArrays(xcfa)
              AssignStmt.of(
                cast(arrays, arrayType),
                cast(
                  ArrayWriteExpr.of(
                    cast(arrays.ref, arrayType),
                    cast(deref.array.getArrayReads(xcfa), arrayType.indexType),
                    ArrayWriteExpr.of(
                      cast(
                        ArrayReadExpr.of(
                          cast(arrays.ref, arrayType),
                          cast(deref.array.getArrayReads(xcfa), arrayType.indexType),
                        ),
                        arrayType.elemType,
                      ),
                      cast(deref.offset.getArrayReads(xcfa), arrayType.elemType.indexType),
                      cast(stmt.expr.getArrayReads(xcfa), arrayType.elemType.elemType),
                    ),
                  ),
                  arrayType,
                ),
              )
            }

            is AssignStmt<*> ->
              AssignStmt.of(
                cast(stmt.varDecl, stmt.varDecl.type),
                cast(stmt.expr.getArrayReads(xcfa), stmt.varDecl.type),
              )

            is AssumeStmt -> AssumeStmt.of(stmt.cond.getArrayReads(xcfa))

            else -> stmt
          },
          choiceType,
          metadata,
        )
      }

      is InvokeLabel ->
        InvokeLabel(
          name,
          params.map { it.getArrayReads(xcfa) },
          metadata,
          tempLookup,
          isLibraryFunction,
        )

      is StartLabel ->
        StartLabel(name, params.map { it.getArrayReads(xcfa) }, pidVar, metadata, tempLookup)

      is ReturnLabel -> ReturnLabel(enclosedLabel.replaceDereferences(xcfa))
      else -> this
    }
  }

  private fun <T : Type> Expr<T>.getArrayReads(xcfa: XcfaBuilder): Expr<T> =
    if (this is Dereference<*, *, *>) {
      val arrayType = ArrayType.of(this.array.type, ArrayType.of(this.offset.type, this.type))
      // (deref array offset) -> arrays[array][offset]
      // -> ArrayRead(ArrayRead(arrays, array), offset)
      ArrayReadExpr.of(
        ArrayReadExpr.of(
          cast(this.getArrays(xcfa).ref, arrayType),
          cast(this.array.getArrayReads(xcfa), this.array.type),
        ),
        cast(this.offset.getArrayReads(xcfa), this.offset.type),
      ) as Expr<T>
    } else {
      withOps(ops.map { it.getArrayReads(xcfa) })
    }

  private val Type.defaultValue: LitExpr<out Type>
    get() =
      when (this) {
        is IntType -> IntLitExpr.of(BigInteger.ZERO)
        is BoolType -> Bool(false)
        is BvType -> BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, size)
        is RatType -> RatLitExpr.of(BigInteger.ZERO, BigInteger.ONE)
        is FpType -> FpUtils.bigFloatToFpLitExpr(BigFloat.zero(significand), this)
        is ArrayType<*, *> ->
          ArrayLitExpr.of(
            listOf(),
            cast(elemType.defaultValue, elemType),
            ArrayType.of(indexType, elemType),
          )
        else -> error("No default value for type $this")
      }
}
