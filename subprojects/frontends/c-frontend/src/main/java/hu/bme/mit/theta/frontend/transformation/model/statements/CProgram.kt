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
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration

class CProgram(parseContext: ParseContext) : CStatement(parseContext) {
  val functions: MutableList<CFunction> = ArrayList()
  val globalDeclarations: MutableList<Tuple2<CDeclaration, VarDecl<*>>> = ArrayList()

  /**
   * The functions this translation unit only ever *declares*, with the variable that stands for
   * each one's address.
   *
   * They have no body here -- they are the library functions (`malloc`, `__VERIFIER_nondet_int`,
   * ...) resolved by name much later -- so they are not among [functions]. Their address can still
   * be taken, exactly like a defined function's, and the variable then has to be initialised to the
   * function's id; without that it is unconstrained, and every *other* candidate's dispatch guard
   * `fp == id(g)` becomes satisfiable on a pointer that in fact holds this function.
   */
  val functionDeclarations: MutableList<Tuple2<CDeclaration, VarDecl<*>>> = ArrayList()

  override fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R =
    visitor.visit(this, param)
}
