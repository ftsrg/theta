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
package hu.bme.mit.theta.ctl

import hu.bme.mit.theta.analysis.algorithm.mdd.ctl.CtlExpr
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.ctl.dsl.gen.CtlDslLexer
import hu.bme.mit.theta.ctl.dsl.gen.CtlDslParser
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer

/** Thrown when a CTL formula cannot be parsed. */
class CtlParseException(message: String) : RuntimeException(message)

/** Parses CTL formulas (the `CtlDsl` grammar) into [CtlExpr] over a given set of variables. */
object CtlParser {

  /** Parses [input] into a [CtlExpr], resolving atoms against [vars] (keyed by name). */
  fun parse(input: String, vars: Map<String, VarDecl<*>>): CtlExpr {
    val lexer = CtlDslLexer(CharStreams.fromString(input))
    val parser = CtlDslParser(CommonTokenStream(lexer))
    val errorListener =
      object : BaseErrorListener() {
        override fun syntaxError(
          recognizer: Recognizer<*, *>?,
          offendingSymbol: Any?,
          line: Int,
          charPositionInLine: Int,
          msg: String?,
          e: RecognitionException?,
        ) {
          throw CtlParseException("Syntax error at $line:$charPositionInLine - $msg")
        }
      }
    lexer.removeErrorListeners()
    lexer.addErrorListener(errorListener)
    parser.removeErrorListeners()
    parser.addErrorListener(errorListener)

    return CtlExprVisitor(vars).visit(parser.model())
  }

  /** Parses [input], resolving atoms against [vars] (keyed by [VarDecl.getName]). */
  fun parse(input: String, vars: Collection<VarDecl<*>>): CtlExpr =
    parse(input, vars.associateBy { it.name })
}
