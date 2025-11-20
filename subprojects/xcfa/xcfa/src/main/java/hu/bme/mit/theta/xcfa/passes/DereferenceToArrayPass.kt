/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.Tuple4
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
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
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.dereferences
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
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
 */
class DereferenceToArrayPass : ProcedurePass {

  private val arraysByType =
    mutableMapOf<Tuple4<Type, Type, Type, Boolean>, VarDecl<out ArrayType2D>>()

  /** Maps a dereference to an identifying type key */
  private fun <A : Type, O : Type, T : Type> Dereference<A, O, T>.getTypeKey(
    xcfa: XcfaBuilder
  ): Tuple4<Type, Type, Type, Boolean> {
    val globalVars = xcfa.getVars().map { it.wrappedVar }
    val isGlobal =
      (array as? RefExpr<*>)?.decl in globalVars ||
        xcfa.getInitProcedures().any { p ->
          p.first.getEdges().any { e ->
            e.label.getFlatLabels().any { l ->
              l is StmtLabel &&
                l.stmt.let { assign ->
                  assign is AssignStmt<*> && assign.varDecl in globalVars && assign.expr == array
                }
            }
          }
        }
    return Tuple4.of(array.type, offset.type, type, isGlobal)
  }

  /** Returns an array from the pre-generated lookup of types */
  private fun <A : Type, O : Type, T : Type> Dereference<A, O, T>.getArrays(
    xcfa: XcfaBuilder
  ): VarDecl<ArrayType<A, ArrayType<O, T>>> {
    val arrayType = ArrayType.of(array.type, ArrayType.of(offset.type, type))

    return cast(arraysByType[getTypeKey(xcfa)]!!, arrayType)
  }

  /** Creates arrays from dereference types */
  private fun createArray(
    key: Tuple4<Type, Type, Type, Boolean>,
    xcfa: XcfaBuilder,
  ): VarDecl<out ArrayType2D> {
    val (derefArrayType, derefOffsetType, derefType, isGlobal) = key
    val arrayType = ArrayType.of(derefArrayType, ArrayType.of(derefOffsetType, derefType))

    val decl =
      Decls.Var("__arrays_${derefArrayType}_${derefOffsetType}_${derefType}_${isGlobal}", arrayType)
    val (globalDecl, initLabel) =
      if (isGlobal) {
        val defaultValue =
          ArrayLitExpr.of(
            listOf(),
            cast(arrayType.elemType.defaultValue, arrayType.elemType),
            arrayType,
          )
        XcfaGlobalVar(decl, defaultValue, atomic = true) to AssignStmtLabel(decl, defaultValue)
      } else {
        XcfaGlobalVar(decl, atomic = true) to StmtLabel(HavocStmt.of(decl))
      }
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
    val types =
      builder
        .getEdges()
        .flatMap { it.label.dereferences }
        .map { it.getTypeKey(builder.parent) }
        .toSet()
    types.forEach { arraysByType[it] = createArray(it, builder.parent) }

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
