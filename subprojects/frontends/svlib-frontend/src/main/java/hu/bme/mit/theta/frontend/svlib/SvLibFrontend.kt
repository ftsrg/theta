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
package hu.bme.mit.theta.frontend.svlib

import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibLexer
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.FileInputStream

class SvLibFrontend(private val procedurePassManager: ProcedurePassManager = ProcedurePassManager()) {

  var generateWitness: Boolean = false
    private set

  fun buildXcfa(input: FileInputStream): XCFA {
    val charStream: CharStream = CharStreams.fromStream(input)
    SvLibUtils.init(charStream)
    val parser = SvLibParser(CommonTokenStream(SvLibLexer(charStream)))
      .apply { errorHandler = BailErrorStrategy() }

    val builder = SvLibXcfaBuilder(procedurePassManager)
    val xcfa = builder.buildXcfa(parser)
    generateWitness = builder.generateWitness

    return xcfa
  }
}
