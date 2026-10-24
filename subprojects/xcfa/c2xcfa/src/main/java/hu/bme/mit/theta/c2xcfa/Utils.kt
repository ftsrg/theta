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
import hu.bme.mit.theta.frontend.transformation.grammar.parseTypeAware
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.model.XCFA
import java.io.File
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
  logger: Logger = warningLogger,
): Triple<XCFA, CStatistics?, Pair<XcfaStatistics, XcfaStatistics>?> {
  val input = CharStreams.fromStream(stream)
  val context = parseTypeAware(input)

  val program = context.accept(FunctionVisitor(parseContext, warningLogger))
  check(program is CProgram)
  logger.benchmark("ParsingResult Success")

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
): Expr<*> {
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
        TypeVisitor(null, TypedefVisitor(null), parseContext, warningLogger),
        warningLogger,
      )
    )

  check(expr is Expr<*>)
  return expr
}

fun getBoolExpressionFromC(
  value: String,
  parseContext: ParseContext,
  collectStatistics: Boolean,
  checkOverflow: Boolean,
  warningLogger: Logger,
  vars: Iterable<VarDecl<*>>,
): Expr<BoolType> {
  val expr =
    getExpressionFromC(value, parseContext, collectStatistics, checkOverflow, warningLogger, vars)
  val signedType = CComplexType.getSignedInt(parseContext)

  return if (
    expr is IteExpr<*> && expr.then == signedType.unitValue && expr.`else` == signedType.nullValue
  ) {
    expr.cond
  } else {
    Neq(expr, signedType.nullValue)
  }
}

/**
 * Builds an XCFA from multiple C translation units (multi-TU verification).
 *
 * Each file is parsed into its own [CProgram], then all programs are merged by combining their
 * functions, global declarations, and function declarations into a single [CProgram] before
 * building the XCFA. This allows verifying C programs whose source is split across multiple
 * .c files, as is common in real projects.
 */
fun getXcfaFromC(
  files: List<File>,
  parseContext: ParseContext,
  collectStatistics: Boolean,
  property: XcfaProperty,
  warningLogger: Logger,
  logger: Logger = warningLogger,
): Triple<XCFA, CStatistics?, Pair<XcfaStatistics, XcfaStatistics>?> {
  val programs = ArrayList<CProgram>()
  for (file in files) {
    val input = CharStreams.fromStream(java.io.FileInputStream(file))
    val context = parseTypeAware(input)
    val program = context.accept(FunctionVisitor(parseContext, warningLogger))
    check(program is CProgram) { "Expected CProgram from $file" }
    programs.add(program)
    logger.benchmark("ParsingResult Success")
  }

  val merged = mergeCPrograms(programs)
  val frontendXcfaBuilder = FrontendXcfaBuilder(parseContext, property, warningLogger)
  val builder = frontendXcfaBuilder.buildXcfa(merged)
  val xcfa = builder.build()

  if (collectStatistics) {
    val programStatistics =
      try {
        merged.getStatistics()
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

/**
 * Merges multiple [CProgram] instances into one by combining their functions, global declarations,
 * and function declarations. Duplicate function names are kept (the first definition wins), while
 * declarations are deduplicated by name.
 */
private fun mergeCPrograms(programs: List<CProgram>): CProgram {
  if (programs.size == 1) return programs[0]

  val merged = CProgram(programs[0].getParseContext())
  val functionNames = HashSet<String>()
  val globalNames = HashSet<String>()
  val funcDeclNames = HashSet<String>()

  for (program in programs) {
    for (function in program.functions) {
      if (!functionNames.contains(function.funcDecl.name)) {
        merged.functions.add(function)
        functionNames.add(function.funcDecl.name)
      }
    }
    for (global in program.globalDeclarations) {
      val name = global.get2().name
      if (!globalNames.contains(name)) {
        merged.globalDeclarations.add(global)
        globalNames.add(name)
      }
    }
    for (funcDecl in program.functionDeclarations) {
      val name = funcDecl.get1().name
      if (!funcDeclNames.contains(name)) {
        merged.functionDeclarations.add(funcDecl)
        funcDeclNames.add(name)
      }
    }
  }
  return merged
}
