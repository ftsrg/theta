/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.frontend.CStatistics
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.getStatistics
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.xcfa.model.XCFA
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.InputStream

fun getXcfaFromC(stream: InputStream, parseContext: ParseContext, collectStatistics: Boolean,
    checkOverflow: Boolean): Triple<XCFA, CStatistics?, Pair<XcfaStatistics, XcfaStatistics>?> {
    val input = CharStreams.fromStream(stream)
    val lexer = CLexer(input)
    val tokens = CommonTokenStream(lexer)
    val parser = CParser(tokens)
    parser.errorHandler = BailErrorStrategy()
    val context = parser.compilationUnit()

    val program = context.accept(FunctionVisitor(parseContext))
    check(program is CProgram)

    val frontendXcfaBuilder = FrontendXcfaBuilder(parseContext, checkOverflow)
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