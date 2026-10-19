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
package hu.bme.mit.theta.frontend.transformation.model.types.simple

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CBool
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CDouble
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CFloat
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CLongDouble
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSigned128
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedShort
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsigned128
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedShort
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid

/** This type either represents a built-in type like int or float, or a typedef'd named type. */
open class NamedType
internal constructor(
  protected val parseContext: ParseContext,
  namedType: String,
  private val uniqueWarningLogger: Logger,
) : CSimpleType() {

  var namedType: String = namedType
    private set

  override val actualType: CComplexType
    get() {
      // isSigned is read as a primitive, as before: an unset signedness fails here.
      var type: CComplexType =
        when (namedType) {
          "char" ->
            if (isSigned!!) CSignedChar(this, parseContext) else CUnsignedChar(this, parseContext)
          "int" ->
            when {
              isBool -> CBool(this, parseContext)
              isSigned!! ->
                when {
                  is128 -> CSigned128(this, parseContext)
                  isLong -> CSignedLong(this, parseContext)
                  isLongLong -> CSignedLongLong(this, parseContext)
                  isShort -> CSignedShort(this, parseContext)
                  else -> CSignedInt(this, parseContext)
                }
              else ->
                when {
                  is128 -> CUnsigned128(this, parseContext)
                  isLong -> CUnsignedLong(this, parseContext)
                  isLongLong -> CUnsignedLongLong(this, parseContext)
                  isShort -> CUnsignedShort(this, parseContext)
                  else -> CUnsignedInt(this, parseContext)
                }
            }
          "double" -> if (isLong) CLongDouble(this, parseContext) else CDouble(this, parseContext)
          "float" -> CFloat(this, parseContext)
          "void" -> CVoid(this, parseContext)
          else -> {
            uniqueWarningLogger.write(
              Level.INFO,
              "WARNING: Unknown simple type " + namedType.replace("%", "%%") + "\n",
            )
            if (namedType.startsWith("enum ")) {
              // An enum whose definition was never seen is still an int in C. The CVoid fallback
              // gave such variables a unit-sized SMT sort, so any assignment to them died casting
              // a full-width value into it.
              CSignedInt(this, parseContext)
            } else {
              CVoid(this, parseContext)
            }
          }
        }
      if (isThreadLocal) {
        type.setThreadLocal()
      }
      // Atomicity belongs to a *level* of the type, so it is put on the level it was written at:
      // the base for `_Atomic int`, a particular pointer for `int * _Atomic`. Until now
      // `CComplexType.setAtomic` was never called at all, and a dereference had no atomicity to
      // read -- which is what made every access through an `_Atomic int *` look like a race.
      if (isAtomic) {
        type.setAtomic()
      }
      for (i in 0 until pointerLevel) {
        type = CPointer(this, type, parseContext)
        if (isAtomicPointer(i)) {
          type.setAtomic()
        }
      }
      return type
    }

  override fun patch(cSimpleType: CSimpleType): CSimpleType {
    for (i in 0 until pointerLevel) {
      cSimpleType.incrementPointer()
    }
    when (namedType) {
      "__int128" -> cSimpleType.is128 = true
      "long" ->
        if (cSimpleType.isLong) {
          cSimpleType.isLongLong = true
          cSimpleType.isLong = false
        } else {
          cSimpleType.isLong = true
        }
      "short" -> cSimpleType.isShort = true
      "_Bool" -> cSimpleType.isBool = true
      "int",
      "char",
      "" -> {}
      "struct" ->
        // we might be a typedef, do nothing; otherwise we cannot patch structness onto another
        // csimpletype, so we reverse the patching
        if (cSimpleType !is Struct) return cSimpleType.patch(copyOf())
      "void" ->
        if (cSimpleType is NamedType && cSimpleType.namedType.isEmpty()) {
          cSimpleType.namedType = namedType
        } else {
          warnIgnored(cSimpleType)
        }
      else -> warnIgnored(cSimpleType)
    }
    return cSimpleType
  }

  private fun warnIgnored(cSimpleType: CSimpleType) {
    if (!cSimpleType.isTypedef) {
      uniqueWarningLogger.write(
        Level.INFO,
        "WARNING: namedType should be short or long or type specifier, instead it is " +
          namedType.replace("%", "%%") +
          "; ignoring it\n",
      )
    }
  }

  override val baseType: CSimpleType
    get() =
      NamedType(parseContext, namedType, uniqueWarningLogger).also {
        it.isAtomic = isAtomic
        it.isExtern = isExtern
        it.isStaticStorage = isStaticStorage
        it.isTypedef = isTypedef
        it.isVolatile = isVolatile
        it.isSigned = isSigned
        it.isShort = isShort
        it.isBool = isBool
        it.isLong = isLong
        it.isLongLong = isLongLong
        it.is128 = is128
      }

  override fun toString(): String {
    val sb = StringBuilder()
    if (isTypedef) sb.append("typedef ")
    if (isExtern) sb.append("extern ")
    if (isVolatile) sb.append("volatile ")
    if (isAtomic) sb.append("_Atomic ")
    if (!isSigned!!) sb.append("unsigned ")
    if (isShort) sb.append("short ")
    if (isLong) sb.append("long ")
    if (isBool) sb.append("_Bool ")
    if (isLongLong) sb.append("long long ")
    sb.append(if (is128) "__int128" else namedType)
    return sb.toString()
  }

  override val isVoid: Boolean
    get() = namedType == "void" && pointerLevel == 0

  override fun copyOf(): CSimpleType =
    NamedType(parseContext, namedType, uniqueWarningLogger).also { setUpCopy(it) }
}
