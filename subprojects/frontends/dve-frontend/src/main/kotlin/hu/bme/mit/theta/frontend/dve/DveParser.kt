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

package hu.bme.mit.theta.frontend.dve

import hu.bme.mit.theta.dve.frontend.dsl.gen.dveLexer
import hu.bme.mit.theta.dve.frontend.dsl.gen.dveParser
import hu.bme.mit.theta.frontend.dve.grammar.DveModelVisitor
import hu.bme.mit.theta.frontend.dve.model.DveModel
import java.io.InputStream
import java.nio.file.Path
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

object DveParser {

    fun parse(input: InputStream): DveModel {
        val charStream = CharStreams.fromStream(input)
        val lexer = dveLexer(charStream)
        val tokens = CommonTokenStream(lexer)
        val parser = dveParser(tokens)
        val tree = parser.model()
        return DveModelVisitor().visitModel(tree)
    }

    fun parse(path: Path): DveModel = path.toFile().inputStream().use { parse(it) }
}
