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
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor
import hu.bme.mit.theta.frontend.transformation.model.statements.CProgram
import hu.bme.mit.theta.xcfa.model.XCFA
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.InputStream

fun getXcfaFromC(stream: InputStream, checkOverflow: Boolean): XCFA {
    val input = CharStreams.fromStream(stream)
    val lexer = CLexer(input)
    val tokens = CommonTokenStream(lexer)
    val parser = CParser(tokens)
    parser.errorHandler = BailErrorStrategy()
    val context = parser.compilationUnit()

    val program = context.accept(FunctionVisitor.instance)
    check(program is CProgram)

    val frontendXcfaBuilder = FrontendXcfaBuilder(checkOverflow)
    val builder = frontendXcfaBuilder.buildXcfa(program)
    return builder.build()
}