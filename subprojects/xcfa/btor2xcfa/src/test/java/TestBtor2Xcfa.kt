import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Lexer
import hu.bme.mit.theta.btor2.frontend.dsl.gen.Btor2Parser
import hu.bme.mit.theta.btor2xcfa.Btor2XcfaBuilder
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.models.Btor2Circuit
import hu.bme.mit.theta.frontend.visitors.Btor2Visitor
import hu.bme.mit.theta.xcfa.model.toDot
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.junit.jupiter.api.Test
import java.io.File

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

class TestBtor2Xcfa {
    @Test
    fun testBtor2Xcfa() {
        val logger = ConsoleLogger(Logger.Level.VERBOSE)
        val visitor = Btor2Visitor()
        val btor2File = File("src/test/resources/count2.btor2")

        val input = btor2File.readLines().joinToString("\n")
        val cinput = CharStreams.fromString(input)
        val lexer = Btor2Lexer(cinput)
        val tokens = CommonTokenStream(lexer)
        val parser = Btor2Parser(tokens)
        parser.errorHandler = BailErrorStrategy()
        val context = parser.btor2()

        context.accept(visitor)

        val xcfa = Btor2XcfaBuilder.btor2xcfa(Btor2Circuit)
        logger.write( Logger.Level.VERBOSE, "XCFA built, result: ", xcfa.toDot())
    }
}