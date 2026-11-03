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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CSignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CSignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble
import java.math.BigInteger
import java.util.ArrayDeque
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class CLiteralTypingTest {

  private fun typeOf(literal: String, arch: ArchitectureType): CComplexType =
    parse(literal, arch).second

  private fun parse(
    literal: String,
    arch: ArchitectureType,
    arithmetic: ArithmeticType = ArithmeticType.efficient,
  ): Pair<Expr<*>, CComplexType> {
    val parseContext = ParseContext()
    parseContext.architecture = arch
    parseContext.arithmetic = arithmetic
    val parser = CParser(CommonTokenStream(CLexer(CharStreams.fromString(literal))))
    parser.errorHandler = BailErrorStrategy()
    val expr =
      parser
        .logicalOrExpression()
        .accept(
          ExpressionVisitor(
            setOf(),
            parseContext,
            null,
            ArrayDeque(listOf(Tuple2.of("", emptyMap<String, VarDecl<*>>()))),
            mapOf(),
            null,
            TypeVisitor(null, TypedefVisitor(null), parseContext, NullLogger.getInstance()),
            NullLogger.getInstance(),
          )
        )
    check(expr is Expr<*>)
    return Pair(expr, CComplexType.getType(expr, parseContext))
  }

  @Test
  fun unsignedSuffixIsRespectedIlp32() {
    // regression: 4294967295UL used to be typed signed long long, ignoring the U suffix
    assertTrue(typeOf("4294967295UL", ArchitectureType.ILP32) is CUnsignedLong)
    assertTrue(typeOf("4294967295U", ArchitectureType.ILP32) is CUnsignedInt)
    assertTrue(typeOf("2147483648U", ArchitectureType.ILP32) is CUnsignedInt)
    assertTrue(typeOf("4294967296U", ArchitectureType.ILP32) is CUnsignedLongLong)
  }

  @Test
  fun unsignedSuffixIsRespectedLp64() {
    assertTrue(typeOf("4294967295UL", ArchitectureType.LP64) is CUnsignedLong)
    assertTrue(typeOf("18446744073709551615UL", ArchitectureType.LP64) is CUnsignedLong)
  }

  @Test
  fun plainDecimalStaysSigned() {
    assertTrue(typeOf("123", ArchitectureType.ILP32) is CSignedInt)
    assertTrue(typeOf("123L", ArchitectureType.ILP32) is CSignedLong)
  }

  @Test
  fun hexLiteralsWithEDigitAreIntegers() {
    // regression: 0xCAFE was routed to the float parser because it contains 'e'
    assertTrue(typeOf("0xCAFE", ArchitectureType.ILP32) is CSignedInt)
    assertTrue(typeOf("0xDEAD", ArchitectureType.ILP32) is CSignedInt)
    assertTrue(typeOf("0xFEL", ArchitectureType.ILP32) is CSignedLong)
  }

  @Test
  fun charLiteralsAreIntegers() {
    // regression: 'e' and '.' used to be routed to the float parser
    assertTrue(typeOf("'e'", ArchitectureType.ILP32) is CSignedInt)
    assertTrue(typeOf("'.'", ArchitectureType.ILP32) is CSignedInt)
  }

  @Test
  fun floatLiteralsStillFloats() {
    assertTrue(typeOf("1.5", ArchitectureType.ILP32) is CDouble)
    assertTrue(typeOf("1e5", ArchitectureType.ILP32) is CDouble)
  }

  @Test
  fun hexOctalAndBinaryMayBeUnsigned() {
    // C11 6.4.4.1p5: without a suffix these try int, unsigned int, long, unsigned long, ...
    assertTrue(typeOf("0x7fffffff", ArchitectureType.ILP32) is CSignedInt)
    assertTrue(typeOf("0x80000000", ArchitectureType.ILP32) is CUnsignedInt)
    assertTrue(typeOf("0xffffffff", ArchitectureType.LP64) is CUnsignedInt)
    assertTrue(typeOf("020000000000", ArchitectureType.ILP32) is CUnsignedInt)
    assertTrue(typeOf("0b10000000000000000000000000000000", ArchitectureType.ILP32) is CUnsignedInt)
    assertTrue(typeOf("0x100000000", ArchitectureType.LP64) is CSignedLong)
    assertTrue(typeOf("0x100000000", ArchitectureType.ILP32) is CSignedLongLong)
    assertTrue(typeOf("0x8000000000000000", ArchitectureType.LP64) is CUnsignedLong)
    assertTrue(typeOf("0x8000000000000000", ArchitectureType.ILP32) is CUnsignedLongLong)
    assertTrue(typeOf("0x80000000L", ArchitectureType.ILP32) is CUnsignedLong)
    assertTrue(typeOf("0x80000000L", ArchitectureType.LP64) is CSignedLong)
    assertTrue(typeOf("0x8000000000000000LL", ArchitectureType.LP64) is CUnsignedLongLong)
    assertTrue(typeOf("0x100000000U", ArchitectureType.LP64) is CUnsignedLong)
  }

  @Test
  fun largeDecimalsStaySigned() {
    assertTrue(typeOf("2147483647", ArchitectureType.LP64) is CSignedInt)
    assertTrue(typeOf("2147483648", ArchitectureType.LP64) is CSignedLong)
    assertTrue(typeOf("2147483648", ArchitectureType.ILP32) is CSignedLongLong)
    assertTrue(typeOf("9223372036854775807", ArchitectureType.LP64) is CSignedLong)
  }

  @Test
  fun longSuffixCountsInEitherOrder() {
    assertTrue(typeOf("1LU", ArchitectureType.LP64) is CUnsignedLong)
    assertTrue(typeOf("1lu", ArchitectureType.ILP32) is CUnsignedLong)
    assertTrue(typeOf("1llu", ArchitectureType.ILP32) is CUnsignedLongLong)
    assertTrue(typeOf("1ULL", ArchitectureType.ILP32) is CUnsignedLongLong)
    assertTrue(typeOf("1LL", ArchitectureType.ILP32) is CSignedLongLong)
  }

  @Test
  fun bitvectorLiteralTakesTheSignednessOfItsType() {
    val (expr, type) = parse("0x80000000", ArchitectureType.LP64, ArithmeticType.bitvector)
    assertTrue(type is CUnsignedInt)
    check(expr is BvLitExpr)
    assertEquals(32, expr.type.size)
    assertFalse(expr.type.signed)
    assertEquals(BigInteger.TWO.pow(31), BvUtils.unsignedBvLitExprToBigInteger(expr))

    val (big, bigType) = parse("0x100000000", ArchitectureType.LP64, ArithmeticType.bitvector)
    assertTrue(bigType is CSignedLong)
    check(big is BvLitExpr)
    assertEquals(64, big.type.size)
    assertEquals(BigInteger.TWO.pow(32), BvUtils.signedBvLitExprToBigInteger(big))
  }

  @Test
  fun widthsMatchArchitecture() {
    assertEquals(32, typeOf("4294967295UL", ArchitectureType.ILP32).width())
    assertEquals(64, typeOf("4294967295UL", ArchitectureType.LP64).width())
  }
}
