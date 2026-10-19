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

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CSignedInt

class CCall(val functionId: String, val params: List<CStatement>, parseContext: ParseContext) :
  CStatement(parseContext) {
  val ret: VarDecl<*>

  init {
    params.forEach { it.setParent(this) }
    val type =
      parseContext.metadata.getMetadataValue(functionId, "cType").orElseGet {
        CSignedInt(null, parseContext)
      } as CComplexType
    ret = Var("call_" + functionId + "_ret" + counter++, type.smtType)
    parseContext.metadata.create(ret.ref, "cType", type)
  }

  override fun <P, R> accept(visitor: CStatementVisitor<P, R>, param: P): R =
    visitor.visit(this, param)
}
