/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.CStatistics
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.getStatistics
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.CCompound
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.XCFA
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.InputStream
import java.util.*

fun getXcfaFromC(
    stream: InputStream, parseContext: ParseContext, collectStatistics: Boolean,
    checkOverflow: Boolean, validation: Boolean = false, warningLogger: Logger
): Triple<XCFA, CStatistics?, Pair<XcfaStatistics, XcfaStatistics>?> {
    val input = CharStreams.fromStream(stream)
    val lexer = CLexer(input)
    val tokens = CommonTokenStream(lexer)
    val parser = CParser(tokens)
    parser.errorHandler = BailErrorStrategy()
    val context = parser.compilationUnit()

    val program = context.accept(FunctionVisitor(parseContext, warningLogger))
    check(program is CProgram)

    val frontendXcfaBuilder = FrontendXcfaBuilder(parseContext, checkOverflow, validation, warningLogger)
    val builder = frontendXcfaBuilder.buildXcfa(program)
    val xcfa = builder.build()

    if (collectStatistics) {
        val programStatistics = try {
            program.getStatistics()
        } catch (_: Exception) {
            CStatistics(0, emptyList())
        }
        val unoptimizedXcfaStatistics = try {
            builder.getStatistics()
        } catch (_: Exception) {
            XcfaStatistics(0, emptyList())
        }
        val optimizedXcfaStatistics = try {
            xcfa.getStatistics()
        } catch (_: Exception) {
            XcfaStatistics(0, emptyList())
        }
        return Triple(xcfa, programStatistics, Pair(unoptimizedXcfaStatistics, optimizedXcfaStatistics))
    }

    return Triple(xcfa, null, null)
}

/**
 * Creates a Theta-expression from a C expression.
 * @param str           the expression to parse
 * @param vars          the variables available to use, with C types (@see TestExpressionParsing)
 * @param scope         the scope to use (retrievable from CMetaData for any metadata-bearing object)
 * @param warningLogger the logger to use for parser warnings
 */
fun parseCExpression(
    str: String,
    vars: Map<VarDecl<*>, CComplexType>,
    scope: List<String>,
    warningLogger: Logger,
): Expr<*> {
    val parseContext = ParseContext()
    val variables: LinkedList<Tuple2<String, MutableMap<String, VarDecl<*>>>> = LinkedList()
    scope.forEach { variables.add(Tuple2.of(it, LinkedHashMap())) }
    val flatVariables: MutableList<VarDecl<*>> = ArrayList()
    for ((varDecl, type) in vars) {
        val name = varDecl.name
        val nameParts = name.split("::")
        val varScope = nameParts.subList(0, nameParts.size - 1)
        if (scope.containsAll(varScope)) {
            variables[nameParts.size - 1].get2()[nameParts.last()] = varDecl
            flatVariables.add(varDecl)
            parseContext.metadata.create(varDecl.ref, "cType", type)
            parseContext.metadata.create(varDecl.name, "cName", nameParts.last())
        }
    }

    val input = CharStreams.fromString(str)
    val lexer = CLexer(input)
    val tokens = CommonTokenStream(lexer)
    val parser = CParser(tokens)
    parser.errorHandler = BailErrorStrategy()
    val context = parser.assignmentExpression()
    val funcVisitor = FunctionVisitor(parseContext, warningLogger, variables, flatVariables)
    val statement = context.accept(funcVisitor) as CCompound

    val preStatements = statement.preStatements
    val postStatements = statement.postStatements
    val statementList = statement.getcStatementList()

    return ExprUtils.simplify(statement.expression)
}