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
package hu.bme.mit.theta.core.type.enumtype

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NullaryExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("EnumLit")
data class EnumLitExpr(override val type: EnumType, val value: String) :
  NullaryExpr<EnumType>(), LitExpr<EnumType> {

  init {
    require(value in type.values) { "Invalid value $value for type ${type.name}" }
  }

  companion object {

    @JvmStatic
    fun of(type: EnumType, literalName: String): EnumLitExpr {
      val value = EnumType.getShortName(literalName)
      return EnumLitExpr(type, value)
    }

    @JvmStatic
    fun eq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
      Bool(l.type == r.type && l.value == r.value)

    @JvmStatic
    fun neq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
      Bool(l.type != r.type || l.value != r.value)
  }

  override fun eval(`val`: Valuation): LitExpr<EnumType> = this

  override fun toString(): String = EnumType.makeLongName(type, value)
}
