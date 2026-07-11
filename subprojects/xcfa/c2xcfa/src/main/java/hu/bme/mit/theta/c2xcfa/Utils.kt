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

import org.antlr.v4.runtime.tree.TerminalNode
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.CharStream
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
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor
import hu.bme.mit.theta.frontend.transformation.grammar.type.TypeVisitor
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

/**
 * Parses C, telling type names apart from ordinary identifiers.
 *
 * The grammar cannot do that on its own: `typedefName` is just `Identifier`, so *any* name may start
 * a type. That is what makes `(a) * b` ambiguous (a cast of a dereference, or a multiplication?), and
 * what makes `void *malloc(size_t);` parse as a declaration of two *variables* -- `malloc` swallowed
 * into the specifiers as a type name, and `size_t` left over as a parenthesized declarator -- rather
 * than as a function.
 *
 * C resolves this with a symbol table, so we make one: a first pass parses the file exactly as before
 * (every identifier may be a type name) purely to harvest its typedef names, and the real parse then
 * accepts only those as types.
 *
 * The first pass must tolerate errors, since the files this is meant to fix are precisely the ones
 * that fail to parse today. And if the type-aware parse fails, we fall back to the old permissive one:
 * a typedef name the first pass failed to spot would otherwise turn a file that parses today into one
 * that does not. Nothing that parses now can start failing.
 */
private fun parseTypeAware(input: CharStream): CParser.CompilationUnitContext {
  val typedefNames = collectTypedefNames(input)
  return try {
    parseC(input, typedefNames)
  } catch (e: Exception) {
    parseC(input, typedefNames = null)
  }
}

/** A parse with `typedefNames` as the type names, or the old any-identifier-is-a-type parse if null. */
private fun parseC(input: CharStream, typedefNames: Set<String>?): CParser.CompilationUnitContext {
  input.seek(0)
  val parser = CParser(CommonTokenStream(CLexer(input)))
  if (typedefNames != null) {
    parser.typedefNames.addAll(typedefNames)
    parser.permissiveTypeNames = false
  }
  parser.errorHandler = BailErrorStrategy()
  return parser.compilationUnit()
}

/**
 * The typedef names of the translation unit, from a permissive parse that tolerates errors.
 *
 * The names are read straight off the parse tree. Running the frontend's own visitors here would be
 * a mistake: they have side effects (registering struct tags, writing `cType` metadata into the
 * shared ParseContext), and running them twice over the same file corrupts the real parse.
 */
private fun collectTypedefNames(input: CharStream): Set<String> {
  input.seek(0)
  val parser = CParser(CommonTokenStream(CLexer(input)))
  parser.removeErrorListeners() // a file that does not parse still tells us its typedefs
  val names = LinkedHashSet<String>()
  val tree =
    try {
      parser.compilationUnit()
    } catch (e: Exception) {
      return names
    }
  tree.collectTypedefNamesInto(names)
  return names
}

private fun ParseTree.collectTypedefNamesInto(names: MutableSet<String>) {
  if (this is CParser.DeclarationContext && isTypedef()) {
    val initDeclarators = initDeclaratorList()?.initDeclarator()
    if (initDeclarators.isNullOrEmpty()) {
      // With every identifier taken for a type name, the declared name is swallowed into the
      // specifier list (`typedef unsigned long size_t;` looks like three type specifiers), so it is
      // the last identifier there.
      declarationSpecifiers()?.lastIdentifier()?.let(names::add)
    } else {
      initDeclarators.forEach { it.declarator()?.declaredName()?.let(names::add) }
    }
  }
  for (i in 0 until childCount) getChild(i).collectTypedefNamesInto(names)
}

private fun CParser.DeclarationContext.isTypedef() =
  declarationSpecifiers()?.declarationSpecifier()?.any { it.text == "typedef" } == true

/** The name a declarator declares: its innermost identifier, e.g. `handler` in `(*handler)(int)`. */
private fun ParseTree.declaredName(): String? {
  if (this is CParser.DirectDeclaratorIdContext) return text
  for (i in 0 until childCount) {
    getChild(i).declaredName()?.let {
      return it
    }
  }
  return null
}

private fun ParseTree.lastIdentifier(): String? {
  if (this is TerminalNode && symbol.type == CParser.Identifier) return text
  for (i in childCount - 1 downTo 0) {
    getChild(i).lastIdentifier()?.let {
      return it
    }
  }
  return null
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
        TypeVisitor(null, TypedefVisitor(null), parseContext, warningLogger),
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
