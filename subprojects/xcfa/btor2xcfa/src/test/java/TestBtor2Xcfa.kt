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
/*
class TestBtor2Xcfa {
  @Test
  fun testBtor2Xcfa() {
    val logger = ConsoleLogger(Logger.Level.VERBOSE)
    val uniqueWarningLogger = UniqueWarningLogger(logger)
    val visitor = Btor2Visitor()
    val btor2File = File("")

    val input = btor2File.readLines().joinToString("\n")
    val cinput = CharStreams.fromString(input)
    val lexer = Btor2Lexer(cinput)
    val tokens = CommonTokenStream(lexer)
    val parser = Btor2Parser(tokens)
    parser.errorHandler = BailErrorStrategy()
    val context = parser.btor2()

    context.accept(visitor)

    val xcfa = Btor2XcfaBuilder.btor2xcfa(uniqueWarningLogger)
    logger.write(Logger.Level.VERBOSE, "XCFA built, result: " + xcfa.toDot() + "\n")
  }
}*/
