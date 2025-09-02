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
package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import kotlinx.serialization.SerializationException
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

class TypeSerializationTest {

  companion object {

    private val json = coreJson

    @JvmStatic
    val bvTypeTestData: List<Arguments> =
      listOf(Arguments.of(42, true), Arguments.of(1, false), Arguments.of(8, null))
  }

  @Test
  fun `test BoolType serialization`() {
    val original: Type = BoolType
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test IntType serialization`() {
    val original: Type = IntType
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @ParameterizedTest
  @MethodSource("getBvTypeTestData")
  fun `test BvType serialization`(size: Int, signed: Boolean?) {
    val original: Type = BvType(size, signed)
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
    val deserializedBvType = deserialized as BvType
    assertEquals(size, deserializedBvType.size)
  }

  @Test
  fun `test ArrayType serialization`() {
    val original: Type = ArrayType(BoolType, IntType)
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)

    val complex: Type =
      ArrayType(
        indexType = BvType(8, false),
        elemType = ArrayType(indexType = ArrayType(IntType, RatType), elemType = BoolType),
      )
    val complexSerialized = json.encodeToString(complex)
    val complexDeserialized = json.decodeFromString<Type>(complexSerialized)
    assertEquals(complex, complexDeserialized)
    assertDoesNotThrow {
      complexDeserialized as ArrayType<BvType, ArrayType<ArrayType<IntType, RatType>, BoolType>>
    }
    assertThrows<ClassCastException> {
      (complexDeserialized as ArrayType<IntType, BvType>).elemType.size
    }
  }

  @Test
  fun `test FuncType serialization`() {
    val original: Type = FuncType(IntType, BoolType)
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test FpType serialization`() {
    val original: Type = FpType(8, 24)
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test RatType serialization`() {
    val original: Type = RatType
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test EnumType serialization`() {
    val original: Type = EnumType.of("Color", listOf("Red", "Green", "Blue"))
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<Type>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test heterogeneous Type collection serialization`() {
    val original: List<Type> =
      listOf(
        BoolType,
        IntType,
        BvType(8, true),
        ArrayType(BoolType, IntType),
        FuncType(IntType, BoolType),
        FpType(8, 24),
        RatType,
        EnumType.of("Color", listOf("Red", "Green", "Blue")),
      )
    val serialized = json.encodeToString(original)
    val deserialized = json.decodeFromString<List<Type>>(serialized)
    assertEquals(original, deserialized)
  }

  @Test
  fun `test specific serializer must ignore type field`() {
    val original: Type = BvType(8, true)
    val serialized = json.encodeToString(original)
    assertDoesNotThrow { (json.decodeFromString<Type>(serialized) as BvType).size }
    assertThrows<SerializationException> { json.decodeFromString<BvType>(serialized).size }

    val jsonIgnoreUnknownKey = Json {
      serializersModule = coreSerializerModule
      classDiscriminator = "class"
      ignoreUnknownKeys = true
    }
    assertDoesNotThrow { jsonIgnoreUnknownKey.decodeFromString<BvType>(serialized).size }
  }
}
