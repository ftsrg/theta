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
package hu.bme.mit.theta.core.type.enumtype

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.core.serialization.TypeReferenceSerializer
import hu.bme.mit.theta.core.type.DomainSize
import hu.bme.mit.theta.core.type.EnumEqExpr
import hu.bme.mit.theta.core.type.EnumLitExpr
import hu.bme.mit.theta.core.type.EnumNeqExpr
import hu.bme.mit.theta.core.type.EqExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.InvalidLitExpr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.Equational
import java.util.regex.Pattern
import kotlinx.serialization.KeepGeneratedSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/** An enumeration type. Like a declaration, it is equal only to itself. */
@Serializable(with = TypeReferenceSerializer::class)
@KeepGeneratedSerializer
@SerialName("enum")
class EnumType private constructor(val name: String, private val valueList: List<String>) :
  Equational<EnumType> {

  @Transient
  private val literals: Map<String, Int> =
    LinkedHashMap<String, Int>().also { map -> valueList.forEachIndexed { i, v -> map[v] = i } }

  override val domainSize: DomainSize
    get() = DomainSize.of(literals.size.toLong())

  override fun Eq(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): EqExpr<EnumType> =
    EnumEqExpr.of(leftOp, rightOp)

  override fun Neq(leftOp: Expr<EnumType>, rightOp: Expr<EnumType>): NeqExpr<EnumType> =
    EnumNeqExpr.of(leftOp, rightOp)

  val values: Set<String>
    get() = literals.keys

  val longValues: Set<String>
    get() = literals.keys.map { makeLongName(this, it) }.toHashSet()

  fun getIntValue(literal: EnumLitExpr): Int = getIntValue(literal.value)

  fun getIntValue(literal: String): Int {
    checkArgument(
      literals.containsKey(literal),
      String.format("Enum type %s does not contain literal '%s'", name, literal),
    )
    return literals.getValue(literal)
  }

  fun litFromShortName(shortName: String): LitExpr<EnumType> =
    try {
      EnumLitExpr.of(this, shortName)
    } catch (e: Exception) {
      throw RuntimeException(String.format("%s is not valid for type %s", shortName, name), e)
    }

  fun litFromLongName(longName: String): LitExpr<EnumType> {
    if (!longName.contains(FULLY_QUALIFIED_NAME_SEPARATOR))
      throw RuntimeException(String.format("%s is an invalid enum longname"))
    val parts = longName.split(Pattern.quote(FULLY_QUALIFIED_NAME_SEPARATOR).toRegex())
    val type = parts[0]
    checkArgument(name == type, String.format("%s does not belong to type %s", type, name))
    return litFromShortName(parts[1])
  }

  fun litFromIntValue(value: Int): LitExpr<EnumType> =
    literals.entries.firstOrNull { it.value == value }?.let { EnumLitExpr.of(this, it.key) }
      ?: InvalidLitExpr(this)

  override fun toString(): String = String.format("EnumType{%s}", name)

  companion object {
    const val FULLY_QUALIFIED_NAME_SEPARATOR = "."

    @JvmStatic
    fun of(name: String, values: Collection<String>): EnumType = EnumType(name, values.toList())

    @JvmStatic
    fun makeLongName(typeName: String, literal: String): String =
      String.format("%s%s%s", typeName, FULLY_QUALIFIED_NAME_SEPARATOR, literal)

    @JvmStatic
    fun makeLongName(type: EnumType, literal: String): String = makeLongName(type.name, literal)

    @JvmStatic
    fun getShortName(longName: String): String =
      if (!longName.contains(FULLY_QUALIFIED_NAME_SEPARATOR)) longName
      else
        longName.substring(
          longName.indexOf(FULLY_QUALIFIED_NAME_SEPARATOR) + FULLY_QUALIFIED_NAME_SEPARATOR.length
        )
  }
}
