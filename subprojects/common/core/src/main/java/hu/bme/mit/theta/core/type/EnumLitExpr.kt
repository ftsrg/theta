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
package hu.bme.mit.theta.core.type

import com.google.common.base.Objects
import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.enumtype.EnumType

class EnumLitExpr private constructor(override val type: EnumType, val value: String) :
  NullaryExpr<EnumType>(), LitExpr<EnumType> {

  override fun eval(valuation: Valuation): LitExpr<EnumType> = this

  override fun toString(): String = EnumType.makeLongName(type.name, value)

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other == null || javaClass != other.javaClass) return false
    val that = other as EnumLitExpr
    return Objects.equal(type, that.type) && Objects.equal(value, that.value)
  }

  override fun hashCode(): Int = Objects.hashCode(type, value)

  companion object {
    @JvmStatic
    fun of(type: EnumType, literalName: String): EnumLitExpr {
      val value = EnumType.getShortName(literalName)
      checkArgument(type.values.contains(value), "Invalid value %s for type %s", value, type.name)
      return EnumLitExpr(type, value)
    }

    @JvmStatic
    fun eq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
      Bool(l.type == r.type && l.value == r.value)

    @JvmStatic
    fun neq(l: EnumLitExpr, r: EnumLitExpr): BoolLitExpr =
      Bool(l.type != r.type || l.value != r.value)
  }
}
