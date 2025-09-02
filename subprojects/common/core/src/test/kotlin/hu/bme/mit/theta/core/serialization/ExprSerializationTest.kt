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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.*
import hu.bme.mit.theta.core.type.arraytype.*
import hu.bme.mit.theta.core.type.booltype.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.enumtype.EnumEqExpr
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.core.type.enumtype.EnumNeqExpr
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.*
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode.*
import hu.bme.mit.theta.core.type.functype.FuncAppExpr
import hu.bme.mit.theta.core.type.functype.FuncLitExpr
import hu.bme.mit.theta.core.type.inttype.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.*
import java.math.BigInteger
import kotlinx.serialization.encodeToString
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

@Suppress("UNCHECKED_CAST")
class ExprSerializationTest {

  companion object {

    private val json = coreJson

    private val bv1 = BvLitExpr(booleanArrayOf(true, false), true)
    private val bv2 = BvLitExpr(booleanArrayOf(false, true))

    private val fp1 = FpLitExpr(false, bv1, bv2)
    private val fp2 = FpLitExpr(false, bv2, bv1)

    private val rat1 = RatLitExpr(BigInteger.valueOf(1), BigInteger.valueOf(2))
    private val rat2 = RatLitExpr(BigInteger.valueOf(3), BigInteger.valueOf(4))

    private val enumType = EnumType("Color", mapOf("Red" to 0, "Green" to 1, "Blue" to 2))

    private val func = FuncLitExpr(Decls.Param("x", Int()), False())
  }

  @Test
  fun `test Dereference serialization`() {
    val expr = Dereference(Int(0), True(), Int())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as Dereference<IntType, BoolType, IntType>).array.type }
  }

  @Test
  fun `test InvalidLitExpr serialization`() {
    val expr = InvalidLitExpr(Int())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertNotEquals(expr, deserialized) // special case, never equal
    assertDoesNotThrow { (deserialized as InvalidLitExpr<IntType>).type }
  }

  @Test
  fun `test IteExpr serialization`() {
    val expr = IteExpr(Eq(Int(0), Int(1)), Int(2), Int(3))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IteExpr<IntType>).then }
  }

  @Test
  fun `test PrimeExpr serialization`() {
    val expr = PrimeExpr(Int(0))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as PrimeExpr<IntType>).op }
  }

  @Test
  fun `test RefExpr serialization`() {
    val expr = RefExpr(Decls.Var("x", Int()))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RefExpr<IntType>).decl }
  }

  @Test
  fun `test Reference serialization`() {
    val expr = Reference(Int(0), Bool())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as Reference<BoolType, IntType>).expr }
  }

  @Test
  fun `test ArrayEqExpr serialization`() {
    val expr =
      ArrayEqExpr(
        ArrayLitExpr(listOf(), Int(0), ArrayType(Bool(), Int())),
        ArrayLitExpr(listOf(), Int(1), ArrayType(Bool(), Int())),
      )
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayEqExpr<BoolType, IntType>).leftOp }
  }

  @Test
  fun `test ArrayInitExpr serialization`() {
    val expr = ArrayInitExpr(listOf(Int(0) to Int(1)), Int(2), ArrayType(Int(), Int()))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayInitExpr<IntType, IntType>).elements }
  }

  @Test
  fun `test ArrayLitExpr serialization`() {
    val expr = ArrayLitExpr(listOf(Int(0) to Int(1)), Int(2), ArrayType(Int(), Int()))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayLitExpr<IntType, IntType>).elements }
  }

  @Test
  fun `test ArrayNeqExpr serialization`() {
    val expr =
      ArrayNeqExpr(
        ArrayLitExpr(listOf(), Int(0), ArrayType(Bool(), Int())),
        ArrayLitExpr(listOf(), Int(1), ArrayType(Bool(), Int())),
      )
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayNeqExpr<BoolType, IntType>).leftOp }
  }

  @Test
  fun `test ArrayReadExpr serialization`() {
    val expr = ArrayReadExpr(ArrayLitExpr(listOf(), Int(0), ArrayType(Int(), Int())), Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayReadExpr<IntType, IntType>).array }
  }

  @Test
  fun `test ArrayWriteExpr serialization`() {
    val expr =
      ArrayWriteExpr(ArrayLitExpr(listOf(), Int(0), ArrayType(Int(), Int())), Int(1), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ArrayWriteExpr<IntType, IntType>).array }
  }

  @Test
  fun `test AndExpr serialization`() {
    val expr = AndExpr(listOf(True(), False()))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as AndExpr).ops }
  }

  @Test
  fun `test FalseExpr serialization`() {
    val expr = False()
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { deserialized as FalseExpr }
  }

  @Test
  fun `test TrueExpr serialization`() {
    val expr = True()
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { deserialized as TrueExpr }
  }

  @Test
  fun `test IffExpr serialization`() {
    val expr = IffExpr(True(), False())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IffExpr).leftOp }
  }

  @Test
  fun `test ImplyExpr serialization`() {
    val expr = ImplyExpr(True(), False())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ImplyExpr).leftOp }
  }

  @Test
  fun `test NotExpr serialization`() {
    val expr = NotExpr(True())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as NotExpr).op }
  }

  @Test
  fun `test OrExpr serialization`() {
    val expr = OrExpr(listOf(True(), False()))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as OrExpr).ops }
  }

  @Test
  fun `test ExistsExpr serialization`() {
    val expr = ExistsExpr(listOf(Decls.Param("x", Int())), True())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ExistsExpr).paramDecls }
  }

  @Test
  fun `test ForallExpr serialization`() {
    val expr = ForallExpr(listOf(Decls.Param("x", Int())), True())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as ForallExpr).paramDecls }
  }

  @Test
  fun `test XorExpr serialization`() {
    val expr = XorExpr(True(), False())
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as XorExpr).leftOp }
  }

  @Test
  fun `test BvAddExpr serialization`() {
    val expr = BvAddExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvAddExpr).ops }
  }

  @Test
  fun `test BvAndExpr serialization`() {
    val expr = BvAndExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvAndExpr).ops }
  }

  @Test
  fun `test BvArithShiftRightExpr serialization`() {
    val expr = BvArithShiftRightExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvArithShiftRightExpr).leftOp }
  }

  @Test
  fun `test BvConcatExpr serialization`() {
    val expr = BvConcatExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvConcatExpr).ops }
  }

  @Test
  fun `test BvEqExpr serialization`() {
    val expr = BvEqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvEqExpr).leftOp }
  }

  @Test
  fun `test BvExtractExpr serialization`() {
    val expr = BvExtractExpr(BvLitExpr(booleanArrayOf(true, false), true), Int(0), Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvExtractExpr).from }
  }

  @Test
  fun `test BvLitExpr serialization`() {
    val expr = BvLitExpr(booleanArrayOf(true, false), true)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvLitExpr).value }
  }

  @Test
  fun `test BvLogicShiftRightExpr serialization`() {
    val expr = BvLogicShiftRightExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvLogicShiftRightExpr).leftOp }
  }

  @Test
  fun `test BvMulExpr serialization`() {
    val expr = BvMulExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvMulExpr).ops }
  }

  @Test
  fun `test BvNegExpr serialization`() {
    val expr = BvNegExpr(BvLitExpr(booleanArrayOf(true, false), true))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvNegExpr).op }
  }

  @Test
  fun `test BvNeqExpr serialization`() {
    val expr = BvNeqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvNeqExpr).leftOp }
  }

  @Test
  fun `test BvNotExpr serialization`() {
    val expr = BvNotExpr(BvLitExpr(booleanArrayOf(true, false), true))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvNotExpr).op }
  }

  @Test
  fun `test BvOrExpr serialization`() {
    val expr = BvOrExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvOrExpr).ops }
  }

  @Test
  fun `test BvPosExpr serialization`() {
    val expr = BvPosExpr(BvLitExpr(booleanArrayOf(true, false), true))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvPosExpr).op }
  }

  @Test
  fun `test BvRotateLeftExpr serialization`() {
    val expr = BvRotateLeftExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvRotateLeftExpr).leftOp }
  }

  @Test
  fun `test BvRotateRightExpr serialization`() {
    val expr = BvRotateRightExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvRotateRightExpr).leftOp }
  }

  @Test
  fun `test BvSDivExpr serialization`() {
    val expr = BvSDivExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSDivExpr).leftOp }
  }

  @Test
  fun `test BvSExtExpr serialization`() {
    val expr = BvSExtExpr(bv1, BvType(16, null))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSExtExpr).op }
  }

  @Test
  fun `test BvSGeqExpr serialization`() {
    val expr = BvSGeqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSGeqExpr).leftOp }
  }

  @Test
  fun `test BvSGtExpr serialization`() {
    val expr = BvSGtExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSGtExpr).leftOp }
  }

  @Test
  fun `test BvSLeqExpr serialization`() {
    val expr = BvSLeqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSLeqExpr).leftOp }
  }

  @Test
  fun `test BvSLtExpr serialization`() {
    val expr = BvSLtExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSLtExpr).leftOp }
  }

  @Test
  fun `test BvSModExpr serialization`() {
    val expr = BvSModExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSModExpr).leftOp }
  }

  @Test
  fun `test BvSRemExpr serialization`() {
    val expr = BvSRemExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSRemExpr).leftOp }
  }

  @Test
  fun `test BvShiftLeftExpr serialization`() {
    val expr = BvShiftLeftExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvShiftLeftExpr).leftOp }
  }

  @Test
  fun `test BvSignChangeExpr serialization`() {
    val expr = BvSignChangeExpr(bv1, BvType(2, false))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSignChangeExpr).op }
  }

  @Test
  fun `test BvSubExpr serialization`() {
    val expr = BvSubExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvSubExpr).leftOp }
  }

  @Test
  fun `test BvUDivExpr serialization`() {
    val expr = BvUDivExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvUDivExpr).leftOp }
  }

  @Test
  fun `test BvUGeqExpr serialization`() {
    val expr = BvUGeqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvUGeqExpr).leftOp }
  }

  @Test
  fun `test BvUGtExpr serialization`() {
    val expr = BvUGtExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvUGtExpr).leftOp }
  }

  @Test
  fun `test BvULeqExpr serialization`() {
    val expr = BvULeqExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvULeqExpr).leftOp }
  }

  @Test
  fun `test BvULtExpr serialization`() {
    val expr = BvULtExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvULtExpr).leftOp }
  }

  @Test
  fun `test BvURemExpr serialization`() {
    val expr = BvURemExpr(bv1, bv2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvURemExpr).leftOp }
  }

  @Test
  fun `test BvXorExpr serialization`() {
    val expr = BvXorExpr(listOf(bv1, bv2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvXorExpr).ops }
  }

  @Test
  fun `test BvZExtExpr serialization`() {
    val expr = BvZExtExpr(bv1, BvType(4, true))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as BvZExtExpr).op }
  }

  @Test
  fun `test EnumEqExpr serialization`() {
    val expr = EnumEqExpr(EnumLitExpr(enumType, "Red"), EnumLitExpr(enumType, "Green"))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as EnumEqExpr).leftOp }
  }

  @Test
  fun `test EnumLitExpr serialization`() {
    val expr = EnumLitExpr(enumType, "Red")
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as EnumLitExpr).value }
  }

  @Test
  fun `test EnumNeqExpr serialization`() {
    val expr = EnumNeqExpr(EnumLitExpr(enumType, "Red"), EnumLitExpr(enumType, "Green"))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as EnumNeqExpr).leftOp }
  }

  @Test
  fun `test FpAbsExpr serialization`() {
    val expr = FpAbsExpr(fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpAbsExpr).op }
  }

  @Test
  fun `test FpAddExpr serialization`() {
    val expr = FpAddExpr(RNA, listOf(fp1, fp2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpAddExpr).roundingMode }
  }

  @Test
  fun `test FpAssignExpr serialization`() {
    val expr = FpAssignExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpAssignExpr).leftOp }
  }

  @Test
  fun `test FpDivExpr serialization`() {
    val expr = FpDivExpr(RNE, fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpDivExpr).leftOp }
  }

  @Test
  fun `test FpEqExpr serialization`() {
    val expr = FpEqExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpEqExpr).leftOp }
  }

  @Test
  fun `test FpFromBvExpr serialization`() {
    val expr = FpFromBvExpr(RTN, bv1, FpType(2, 2), false)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpFromBvExpr).op }
  }

  @Test
  fun `test FpGeqExpr serialization`() {
    val expr = FpGeqExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpGeqExpr).leftOp }
  }

  @Test
  fun `test FpGtExpr serialization`() {
    val expr = FpGtExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpGtExpr).leftOp }
  }

  @Test
  fun `test FpIsInfiniteExpr serialization`() {
    val expr = FpIsInfiniteExpr(fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpIsInfiniteExpr).op }
  }

  @Test
  fun `test FpIsNanExpr serialization`() {
    val expr = FpIsNanExpr(fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpIsNanExpr).op }
  }

  @Test
  fun `test FpLeqExpr serialization`() {
    val expr = FpLeqExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpLeqExpr).leftOp }
  }

  @Test
  fun `test FpLitExpr serialization`() {
    val expr = fp1
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpLitExpr).exponent }
  }

  @Test
  fun `test FpLtExpr serialization`() {
    val expr = FpLtExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpLtExpr).leftOp }
  }

  @Test
  fun `test FpMaxExpr serialization`() {
    val expr = FpMaxExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpMaxExpr).leftOp }
  }

  @Test
  fun `test FpMinExpr serialization`() {
    val expr = FpMinExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpMinExpr).leftOp }
  }

  @Test
  fun `test FpMulExpr serialization`() {
    val expr = FpMulExpr(RTP, listOf(fp1, fp2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpMulExpr).ops }
  }

  @Test
  fun `test FpNegExpr serialization`() {
    val expr = FpNegExpr(fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpNegExpr).op }
  }

  @Test
  fun `test FpNeqExpr serialization`() {
    val expr = FpNeqExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpNeqExpr).leftOp }
  }

  @Test
  fun `test FpPosExpr serialization`() {
    val expr = FpPosExpr(fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpPosExpr).op }
  }

  @Test
  fun `test FpRemExpr serialization`() {
    val expr = FpRemExpr(fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpRemExpr).leftOp }
  }

  @Test
  fun `test FpRoundToIntegralExpr serialization`() {
    val expr = FpRoundToIntegralExpr(RTZ, fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpRoundToIntegralExpr).op }
  }

  @Test
  fun `test FpSqrtExpr serialization`() {
    val expr = FpSqrtExpr(RNE, fp1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpSqrtExpr).op }
  }

  @Test
  fun `test FpSubExpr serialization`() {
    val expr = FpSubExpr(RNE, fp1, fp2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpSubExpr).leftOp }
  }

  @Test
  fun `test FpToBvExpr serialization`() {
    val expr = FpToBvExpr(RNE, fp1, 8, true)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpToBvExpr).op }
  }

  @Test
  fun `test FpToFpExpr serialization`() {
    val expr = FpToFpExpr(RNE, fp1, 8, 24)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FpToFpExpr).op }
  }

  @Test
  fun `test FuncAppExpr serialization`() {
    val expr = FuncAppExpr(func, Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FuncAppExpr<IntType, BoolType>).func }
  }

  @Test
  fun `test FuncLitExpr serialization`() {
    val expr = func
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as FuncLitExpr<IntType, BoolType>).result }
  }

  @Test
  fun `test IntAddExpr serialization`() {
    val expr = IntAddExpr(listOf(Int(1), Int(2)))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntAddExpr).ops }
  }

  @Test
  fun `test IntDivExpr serialization`() {
    val expr = IntDivExpr(Int(4), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntDivExpr).leftOp }
  }

  @Test
  fun `test IntEqExpr serialization`() {
    val expr = IntEqExpr(Int(1), Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntEqExpr).leftOp }
  }

  @Test
  fun `test IntGeqExpr serialization`() {
    val expr = IntGeqExpr(Int(2), Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntGeqExpr).leftOp }
  }

  @Test
  fun `test IntGtExpr serialization`() {
    val expr = IntGtExpr(Int(2), Int(1))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntGtExpr).leftOp }
  }

  @Test
  fun `test IntLeqExpr serialization`() {
    val expr = IntLeqExpr(Int(1), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntLeqExpr).leftOp }
  }

  @Test
  fun `test IntLitExpr serialization`() {
    val expr = Int(42)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntLitExpr).value }
  }

  @Test
  fun `test IntLtExpr serialization`() {
    val expr = IntLtExpr(Int(1), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntLtExpr).leftOp }
  }

  @Test
  fun `test IntModExpr serialization`() {
    val expr = IntModExpr(Int(5), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntModExpr).leftOp }
  }

  @Test
  fun `test IntMulExpr serialization`() {
    val expr = IntMulExpr(listOf(Int(2), Int(3)))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntMulExpr).ops }
  }

  @Test
  fun `test IntNegExpr serialization`() {
    val expr = IntNegExpr(Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntNegExpr).op }
  }

  @Test
  fun `test IntNeqExpr serialization`() {
    val expr = IntNeqExpr(Int(1), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntNeqExpr).leftOp }
  }

  @Test
  fun `test IntPosExpr serialization`() {
    val expr = IntPosExpr(Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntPosExpr).op }
  }

  @Test
  fun `test IntRemExpr serialization`() {
    val expr = IntRemExpr(Int(5), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntRemExpr).leftOp }
  }

  @Test
  fun `test IntSubExpr serialization`() {
    val expr = IntSubExpr(Int(5), Int(2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntSubExpr).leftOp }
  }

  @Test
  fun `test IntToRatExpr serialization`() {
    val expr = IntToRatExpr(Int(5))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as IntToRatExpr).op }
  }

  @Test
  fun `test RatAddExpr serialization`() {
    val expr = RatAddExpr(listOf(rat1, rat2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatAddExpr).ops }
  }

  @Test
  fun `test RatDivExpr serialization`() {
    val expr = RatDivExpr(rat1, rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatDivExpr).leftOp }
  }

  @Test
  fun `test RatEqExpr serialization`() {
    val expr = RatEqExpr(rat1, rat1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatEqExpr).leftOp }
  }

  @Test
  fun `test RatGeqExpr serialization`() {
    val expr = RatGeqExpr(rat2, rat1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatGeqExpr).leftOp }
  }

  @Test
  fun `test RatGtExpr serialization`() {
    val expr = RatGtExpr(rat2, rat1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatGtExpr).leftOp }
  }

  @Test
  fun `test RatLeqExpr serialization`() {
    val expr = RatLeqExpr(rat1, rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatLeqExpr).leftOp }
  }

  @Test
  fun `test RatLitExpr serialization`() {
    val expr = rat1
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatLitExpr).denom }
  }

  @Test
  fun `test RatLtExpr serialization`() {
    val expr = RatLtExpr(rat1, rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatLtExpr).leftOp }
  }

  @Test
  fun `test RatMulExpr serialization`() {
    val expr = RatMulExpr(listOf(rat1, rat2))
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatMulExpr).ops }
  }

  @Test
  fun `test RatNegExpr serialization`() {
    val expr = RatNegExpr(rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatNegExpr).op }
  }

  @Test
  fun `test RatNeqExpr serialization`() {
    val expr = RatNeqExpr(rat1, rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatNeqExpr).leftOp }
  }

  @Test
  fun `test RatPosExpr serialization`() {
    val expr = RatPosExpr(rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatPosExpr).op }
  }

  @Test
  fun `test RatSubExpr serialization`() {
    val expr = RatSubExpr(rat2, rat1)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatSubExpr).leftOp }
  }

  @Test
  fun `test RatToIntExpr serialization`() {
    val expr = RatToIntExpr(rat2)
    val serialized = json.encodeToString<Expr<out Type>>(expr)
    val deserialized = json.decodeFromString<Expr<out Type>>(serialized)
    assertEquals(expr, deserialized)
    assertDoesNotThrow { (deserialized as RatToIntExpr).op }
  }
}
