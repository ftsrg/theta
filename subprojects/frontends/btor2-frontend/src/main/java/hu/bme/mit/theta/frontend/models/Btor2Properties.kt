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
package hu.bme.mit.theta.frontend.models

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv
import hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq
import hu.bme.mit.theta.core.type.bvtype.BvType

data class Btor2Bad(override val nid: UInt, override val sort: Btor2Sort?, val operand: Btor2Node) :
  Btor2Node(nid, null) {

  override fun getVar(): VarDecl<*>? {
    return null
  }

  override fun getExpr(): Expr<BoolType> {
    return Eq(operand.getVar()?.ref as RefExpr<BvType>, BvExprs.Bv(BooleanArray(1, { true })))
  }

  override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param: P): R {
    return visitor.visit(this, param)
  }

  fun getStmt(): Stmt {
    return AssumeStmt.of(getExpr())
  }
}
