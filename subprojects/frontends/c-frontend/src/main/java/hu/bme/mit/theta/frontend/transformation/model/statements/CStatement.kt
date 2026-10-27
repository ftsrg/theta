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
package hu.bme.mit.theta.frontend.transformation.model.statements

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import java.util.Optional
import org.antlr.v4.runtime.ParserRuleContext

/**
 * Every Program, Function and Statement is a subclass of this base class. Any CStatement might have
 * an id associated with it, in case there was a label in the source code. This also provides an
 * XcfaLocation, which can be used when jumping to this named location via a _goto_ instruction
 */
sealed class CStatement(protected val parseContext: ParseContext) {
  private var parentStatement: CStatement? = null

  var id: String? = null

  var lineNumberStart = -1
  var colNumberStart = -1
  var lineNumberStop = -1
  var colNumberStop = -1
  var offsetStart = -1
  var offsetEnd = -1
  var functionName: String = ""
  var sourceText: String = ""
  var ctx: ParserRuleContext? = null

  /** Only [CCompound]s can currently have pre- and post statements. */
  open var preStatements: CStatement?
    get() = null
    set(value) {
      throw UnsupportedFrontendElementException(
        "Only CCompounds shall currently have pre- and post statements!"
      )
    }

  open var postStatements: CStatement?
    get() = null
    set(value) {
      throw UnsupportedFrontendElementException(
        "Only CCompounds shall currently have pre- and post statements!"
      )
    }

  fun getParent(): Optional<CStatement> = Optional.ofNullable(parentStatement)

  fun setParent(parent: CStatement) {
    parentStatement = parent
  }

  /**
   * Returns the expression associated with a CStatement, which by default throws an exception, as
   * not all subtypes will return one. For example, the C language statement `int a = (b = 0, 2)`
   * will create a CCompound statement as the right-hand side of the assignment, whose associated
   * expression will be 2, but the assignment to b has to come beforehand. Null when the parser
   * produced no expression for it (e.g. a [CExpr] built from an expression the visitor declined).
   */
  open val expression: Expr<*>?
    get() = throw UnsupportedFrontendElementException("Cannot get expression!")

  abstract fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R

  internal companion object {
    var counter = 0
  }
}
