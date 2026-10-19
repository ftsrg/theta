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

import hu.bme.mit.theta.common.Tuple2
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import java.util.Optional

// TODO: designators
class CInitializerList(val type: CComplexType?, parseContext: ParseContext) :
  CStatement(parseContext) {
  val statements: MutableList<Tuple2<Optional<CStatement>, CStatement>> = ArrayList()

  override val expression: Expr<*>
    get() =
      throw UnsupportedFrontendElementException("Cannot create expression of initializer list.")

  fun addStatement(index: CStatement?, value: CStatement) {
    statements.add(Tuple2.of(Optional.ofNullable(index), value))
  }

  override fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R =
    visitor.visit(this, param)
}
