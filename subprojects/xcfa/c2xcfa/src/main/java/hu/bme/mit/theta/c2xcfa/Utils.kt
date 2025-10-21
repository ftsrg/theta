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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.frontend.CStatistics
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.getStatistics
import hu.bme.mit.theta.frontend.transformation.grammar.expression.ExpressionVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.InputStream
import java.util.ArrayDeque
import kotlin.jvm.optionals.getOrDefault
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

fun getXcfaFromC(
  stream: InputStream,
  parseContext: ParseContext,
  collectStatistics: Boolean,
  property: XcfaProperty,
  warningLogger: Logger,
): Triple<XCFA, CStatistics?, Pair<XcfaStatistics, XcfaStatistics>?> {
  val input = CharStreams.fromStream(stream)
  val lexer = CLexer(input)
  val tokens = CommonTokenStream(lexer)
  val parser = CParser(tokens)
  parser.errorHandler = BailErrorStrategy()
  val context = parser.compilationUnit()

  val program = context.accept(FunctionVisitor(parseContext, warningLogger))
  check(program is CProgram)

  val frontendXcfaBuilder = FrontendXcfaBuilder(parseContext, property, warningLogger)
  val builder = frontendXcfaBuilder.buildXcfa(program)
  val xcfa = builder.build()

  if (collectStatistics) {
    val programStatistics =
      try {
        program.getStatistics()
      } catch (_: Exception) {
        CStatistics(0, emptyList())
      }
    val unoptimizedXcfaStatistics =
      try {
        builder.getStatistics()
      } catch (_: Exception) {
        XcfaStatistics(0, emptyList())
      }
    val optimizedXcfaStatistics =
      try {
        xcfa.getStatistics()
      } catch (_: Exception) {
        XcfaStatistics(0, emptyList())
      }
    return Triple(xcfa, programStatistics, Pair(unoptimizedXcfaStatistics, optimizedXcfaStatistics))
  }

  return Triple(xcfa, null, null)
}

fun getExpressionFromC(
  value: String,
  parseContext: ParseContext,
  collectStatistics: Boolean,
  checkOverflow: Boolean,
  warningLogger: Logger,
  vars: Iterable<VarDecl<*>>,
): Expr<BoolType> {
  val input = CharStreams.fromString(value)
  val lexer = CLexer(input)
  val tokens = CommonTokenStream(lexer)
  val parser = CParser(tokens)
  parser.errorHandler = BailErrorStrategy()
  val context = parser.logicalOrExpression()

  val variables =
    Tuple2.of(
      "",
      vars.associateBy {
        parseContext.metadata.getMetadataValue(it.name, "cName").getOrDefault(it.name) as String
      },
    )

  val expr =
    context.accept(
      ExpressionVisitor(
        setOf(),
        parseContext,
        null,
        ArrayDeque(listOf(variables)),
        mapOf(),
        null,
        null,
        warningLogger,
      )
    )

  check(expr is Expr<*>)
  val signedType = CComplexType.getSignedInt(parseContext)
  if (
    expr is IteExpr<*> && expr.then == signedType.unitValue && expr.`else` == signedType.nullValue
  ) {
    return expr.cond
  } else {
    return Neq(expr, signedType.nullValue)
  }
}
