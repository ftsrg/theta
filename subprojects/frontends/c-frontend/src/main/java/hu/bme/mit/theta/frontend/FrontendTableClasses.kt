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
package hu.bme.mit.theta.frontend

import hu.bme.mit.theta.core.serialization.TableClass
import hu.bme.mit.theta.core.serialization.TableClasses
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CArray
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CBool
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CDouble
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CFloat
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CFunction
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CLongDouble
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSigned128
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedShort
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsigned128
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedChar
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedShort
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.Fitsall

/**
 * Every class of the C frontend that an object table holds: the C types and the expressions the
 * frontend defines. `XcfaSerializationCoverageTest` checks that none is missing.
 */
object FrontendTableClasses : TableClasses() {
  override val names: Set<String> =
    setOf(
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CFunction",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSigned128",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsigned128",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CArray",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CBool",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedChar",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedChar",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedInt",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedInt",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLong",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLong",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLongLong",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLongLong",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedShort",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedShort",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.Fitsall",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CDouble",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CFloat",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CLongDouble",
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid",
      "hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer",
    )

  override fun entry(name: String): TableClass =
    when (name) {
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CFunction" ->
        TableClass(CFunction::class.java, CFunction.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSigned128" ->
        TableClass(CSigned128::class.java, CSigned128.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsigned128" ->
        TableClass(CUnsigned128::class.java, CUnsigned128.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CArray" ->
        TableClass(CArray::class.java, CArray.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CBool" ->
        TableClass(CBool::class.java, CBool.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedChar" ->
        TableClass(CSignedChar::class.java, CSignedChar.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedChar" ->
        TableClass(CUnsignedChar::class.java, CUnsignedChar.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedInt" ->
        TableClass(CSignedInt::class.java, CSignedInt.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedInt" ->
        TableClass(CUnsignedInt::class.java, CUnsignedInt.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLong" ->
        TableClass(CSignedLong::class.java, CSignedLong.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLong" ->
        TableClass(CUnsignedLong::class.java, CUnsignedLong.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedLongLong" ->
        TableClass(CSignedLongLong::class.java, CSignedLongLong.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedLongLong" ->
        TableClass(CUnsignedLongLong::class.java, CUnsignedLongLong.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CPointer" ->
        TableClass(CPointer::class.java, CPointer.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedShort" ->
        TableClass(CSignedShort::class.java, CSignedShort.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CUnsignedShort" ->
        TableClass(CUnsignedShort::class.java, CUnsignedShort.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CStruct" ->
        TableClass(CStruct::class.java, CStruct.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.Fitsall" ->
        TableClass(Fitsall::class.java, Fitsall.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CDouble" ->
        TableClass(CDouble::class.java, CDouble.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CFloat" ->
        TableClass(CFloat::class.java, CFloat.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CLongDouble" ->
        TableClass(CLongDouble::class.java, CLongDouble.serializer())
      "hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid" ->
        TableClass(CVoid::class.java, CVoid.serializer())
      "hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer" ->
        TableClass(UnsupportedInitializer::class.java, UnsupportedInitializer.serializer())
      else -> error("No entry for $name")
    }
}
