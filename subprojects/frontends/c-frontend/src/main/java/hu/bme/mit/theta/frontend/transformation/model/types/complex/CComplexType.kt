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
package hu.bme.mit.theta.frontend.transformation.model.types.complex

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.AddExpr
import hu.bme.mit.theta.core.type.DivExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.ModExpr
import hu.bme.mit.theta.core.type.MulExpr
import hu.bme.mit.theta.core.type.NegExpr
import hu.bme.mit.theta.core.type.PosExpr
import hu.bme.mit.theta.core.type.SourceType
import hu.bme.mit.theta.core.type.SubExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getCastVisitor
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getLimitVisitor
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getNullValueVisitor
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getTypeVisitor
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getUnitValueVisitor
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getValueVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType

sealed class CComplexType(val origin: CSimpleType?, val parseContext: ParseContext) : SourceType {
  private var threadLocal = false
  private var atomic = false

  val nullValue: LitExpr<*>
    get() {
      val accept = accept(getNullValueVisitor(parseContext), null)
      parseContext.metadata.create(accept, "cType", this)
      return accept
    }

  val unitValue: LitExpr<*>
    get() {
      val accept = accept(getUnitValueVisitor(parseContext), null)
      parseContext.metadata.create(accept, "cType", this)
      return accept
    }

  fun getValue(value: String): LitExpr<*> {
    val accept = accept(getValueVisitor(parseContext), value)
    parseContext.metadata.create(accept, "cType", this)
    return accept
  }

  fun limit(expr: Expr<*>): AssumeStmt = accept(getLimitVisitor(parseContext), expr)

  fun castTo(expr: Expr<*>): Expr<*> {
    // The cast may be skipped only when it truly cannot change the value: the expression is
    // already recorded as this type *and* it is not an arithmetic result.
    //
    // Matching types alone is not enough. A cast is what holds a value inside its type's range:
    // `unsigned + unsigned` is *typed* unsigned, but in the unbounded integers its value stands one
    // past the maximum until the cast's modulo wraps it -- and the additive visitor stamps the sum
    // with its result type *before* casting it. Short-circuiting on the recorded type alone
    // therefore skipped the very modulo that performs the wraparound, and `UINT_MAX + 1` quietly
    // stopped coming back to 0.
    if (getType(expr, parseContext) == this && !isArithmetic(expr)) {
      return expr
    }
    val accept = accept(getCastVisitor(parseContext), expr)
    parseContext.metadata.create(accept, "cType", this)
    return accept
  }

  val smtType: Type
    get() = accept(getTypeVisitor(parseContext), null)

  open fun getSmallestCommonType(type: CComplexType): CComplexType =
    throw RuntimeException("Common type is not applicable for this type!")

  open val typeName: String
    get() = throw RuntimeException("Type name could not be queried from this type: $this")

  open fun width(): Int = parseContext.architecture.getBitWidth(typeName)

  fun setThreadLocal() {
    threadLocal = true
  }

  val isThreadLocal: Boolean
    get() = threadLocal

  fun setAtomic() {
    atomic = true
  }

  val isAtomic: Boolean
    get() = atomic

  open fun <T, R> accept(visitor: CComplexTypeVisitor<T, R>, param: T): R =
    visitor.visit(this, param)

  open class CComplexTypeVisitor<T, R> {
    open fun visit(type: CComplexType, param: T): R =
      throw UnsupportedFrontendElementException(
        "Not (yet) implemented (" + type.javaClass.simpleName + " in " + javaClass.name + ")"
      )

    open fun visit(type: CVoid, param: T): R = visit(type as CComplexType, param)

    open fun visit(type: CReal, param: T): R = visit(type as CComplexType, param)

    open fun visit(type: CDouble, param: T): R = visit(type as CReal, param)

    open fun visit(type: CFloat, param: T): R = visit(type as CReal, param)

    open fun visit(type: CLongDouble, param: T): R = visit(type as CReal, param)

    open fun visit(type: CInteger, param: T): R = visit(type as CComplexType, param)

    open fun visit(type: CShort, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CSignedShort, param: T): R = visit(type as CShort, param)

    open fun visit(type: CUnsignedShort, param: T): R = visit(type as CShort, param)

    open fun visit(type: C128, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CLongLong, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CSignedLongLong, param: T): R = visit(type as CLongLong, param)

    open fun visit(type: CSigned128, param: T): R = visit(type as C128, param)

    open fun visit(type: Fitsall, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CUnsigned128, param: T): R = visit(type as C128, param)

    open fun visit(type: CUnsignedLongLong, param: T): R = visit(type as CLongLong, param)

    open fun visit(type: CLong, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CUnsignedLong, param: T): R = visit(type as CLong, param)

    open fun visit(type: CSignedLong, param: T): R = visit(type as CLong, param)

    open fun visit(type: CInt, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CSignedInt, param: T): R = visit(type as CInt, param)

    open fun visit(type: CUnsignedInt, param: T): R = visit(type as CInt, param)

    open fun visit(type: CChar, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CSignedChar, param: T): R = visit(type as CChar, param)

    open fun visit(type: CUnsignedChar, param: T): R = visit(type as CChar, param)

    open fun visit(type: CBool, param: T): R = visit(type as CInteger, param)

    open fun visit(type: CCompound, param: T): R = visit(type as CComplexType, param)

    open fun visit(type: CArray, param: T): R =
      getUnsignedLong(type.parseContext).accept(this, param)

    open fun visit(type: CFunction, param: T): R = visit(type as CCompound, param)

    open fun visit(type: CStruct, param: T): R =
      getUnsignedLong(type.parseContext).accept(this, param)

    open fun visit(type: CPointer, param: T): R =
      getUnsignedLong(type.parseContext).accept(this, param)
  }

  companion object {

    /**
     * Whether evaluating this expression can carry its value out of its own type's range -- i.e.
     * whether a cast to that type still has work to do. An arithmetic result can (that is what the
     * cast's wraparound is for); a variable, a literal or an already-cast value cannot.
     */
    private fun isArithmetic(expr: Expr<*>): Boolean {
      var e = expr
      while (e is PosExpr<*>) {
        e = e.op
      }
      return e is AddExpr<*> ||
        e is SubExpr<*> ||
        e is MulExpr<*> ||
        e is DivExpr<*> ||
        e is ModExpr<*> ||
        e is NegExpr<*>
    }

    @JvmStatic
    fun getSmallestCommonType(types: List<CComplexType>, parseContext: ParseContext): CComplexType {
      var ret = getSignedInt(parseContext)
      for (type in types) {
        ret = ret.getSmallestCommonType(type)
      }
      return ret
    }

    @JvmStatic
    fun getType(s: String, parseContext: ParseContext): CComplexType? =
      when (s) {
        "_Bool" -> CBool(null, parseContext)
        "char",
        "signedchar" -> CSignedChar(null, parseContext)
        "short",
        "signedshort" -> CSignedShort(null, parseContext)
        "unsignedshort" -> CUnsignedShort(null, parseContext)
        "unsignedchar" -> CUnsignedChar(null, parseContext)
        "signed",
        "int",
        "signedint" -> CSignedInt(null, parseContext)
        "unsigned",
        "unsignedint" -> CUnsignedInt(null, parseContext)
        "long",
        "signedlong",
        "longint",
        "signedlongint" -> CSignedLong(null, parseContext)
        "unsignedlong",
        "unsignedlongint" -> CUnsignedLong(null, parseContext)
        "longlong",
        "signedlonglong",
        "lonlongint",
        "signedlonglongint" -> CSignedLongLong(null, parseContext)
        "unsignedlonglong",
        "unsignedlonglongint" -> CUnsignedLongLong(null, parseContext)
        "float" -> CFloat(null, parseContext)
        "double" -> CDouble(null, parseContext)
        "longdouble" -> CLongDouble(null, parseContext)
        else -> if (s.endsWith("*")) CPointer(null, null, parseContext) else null
      }

    @JvmStatic
    fun getType(expr: Expr<*>, parseContext: ParseContext): CComplexType {
      val cTypeOptional = parseContext.metadata.getMetadataValue(expr, "cType")
      return when (val cType = cTypeOptional.orElse(null)) {
        is CComplexType -> cType
        is CSimpleType -> cType.actualType
        else -> getType(expr.type, parseContext)
      }
    }

    private fun getType(type: Type, parseContext: ParseContext): CComplexType {
      return when (type) {
        is IntType -> CSignedInt(null, parseContext)
        is ArrayType<*, *> -> CArray(null, getType(type.elemType, parseContext), parseContext)
        is BoolType -> CBool(null, parseContext)
        is FpType -> {
          val arch = parseContext.architecture
          when (type) {
            FpType.of(arch.getBitWidth("double_e"), arch.getBitWidth("double_s")) ->
              CDouble(null, parseContext)
            FpType.of(arch.getBitWidth("float_e"), arch.getBitWidth("float_s")) ->
              CFloat(null, parseContext)
            FpType.of(arch.getBitWidth("longdouble_e"), arch.getBitWidth("longdouble_s")) ->
              CFloat(null, parseContext)
            else ->
              throw UnsupportedFrontendElementException("No suitable size found for type: $type")
          }
        }
        is BvType -> {
          for ((s, integer) in parseContext.architecture.standardTypeSizes) {
            if (integer == type.size) {
              when (s) {
                "bool" -> return CBool(null, parseContext)
                // Was missing, so *every* 8-bit bitvector fell through this switch and out of the
                // loop to the throw below -- `char` is the first entry whose width is 8. Any
                // `unsigned char` value under bitvector arithmetic therefore died with "No
                // suitable width found for type: (Bv 8)", including plain `unsigned char`
                // bitfields with no initializer in sight, and three ldv-linux tasks that reached
                // it through a portfolio configuration in the 2026-07-20 run.
                "char" ->
                  return if (type.signed) CSignedChar(null, parseContext)
                  else CUnsignedChar(null, parseContext)
                "short" ->
                  return if (type.signed) CSignedShort(null, parseContext)
                  else CUnsignedShort(null, parseContext)
                "int" ->
                  return if (type.signed) CSignedInt(null, parseContext)
                  else CUnsignedInt(null, parseContext)
                "long" ->
                  return if (type.signed) CSignedLong(null, parseContext)
                  else CUnsignedLong(null, parseContext)
                "longlong" ->
                  return if (type.signed) CSignedLongLong(null, parseContext)
                  else CUnsignedLongLong(null, parseContext)
                "__int128" ->
                  return if (type.signed) CSigned128(null, parseContext)
                  else CUnsigned128(null, parseContext)
              }
            }
          }
          throw UnsupportedFrontendElementException("No suitable width found for type: $type")
        }
        else -> throw UnsupportedFrontendElementException("Not yet implemented for type: $type")
      }
    }

    @JvmStatic
    fun getSignedInt(parseContext: ParseContext): CComplexType = CSignedInt(null, parseContext)

    @JvmStatic
    fun getUnsigned128(parseContext: ParseContext): CComplexType = CUnsigned128(null, parseContext)

    @JvmStatic
    fun getUnsignedLongLong(parseContext: ParseContext): CComplexType =
      CUnsignedLongLong(null, parseContext)

    @JvmStatic
    fun getUnsignedLong(parseContext: ParseContext): CComplexType =
      CUnsignedLong(null, parseContext)

    @JvmStatic
    fun getUnsignedInt(parseContext: ParseContext): CComplexType = CUnsignedInt(null, parseContext)

    @JvmStatic
    fun getSigned128(parseContext: ParseContext): CComplexType = CSigned128(null, parseContext)

    @JvmStatic
    fun getSignedLongLong(parseContext: ParseContext): CComplexType =
      CSignedLongLong(null, parseContext)

    @JvmStatic
    fun getSignedLong(parseContext: ParseContext): CComplexType = CSignedLong(null, parseContext)

    @JvmStatic fun getFloat(parseContext: ParseContext): CComplexType = CFloat(null, parseContext)

    @JvmStatic fun getDouble(parseContext: ParseContext): CComplexType = CDouble(null, parseContext)

    @JvmStatic
    fun getLongDouble(parseContext: ParseContext): CComplexType = CLongDouble(null, parseContext)

    @JvmStatic
    fun getFitsall(parseContext: ParseContext): CComplexType = Fitsall(null, parseContext)
  }
}
