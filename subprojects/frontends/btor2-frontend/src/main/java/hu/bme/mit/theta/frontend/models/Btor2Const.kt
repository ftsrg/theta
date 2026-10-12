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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType

data class Btor2Const(
  override val nid: UInt,
  val value: BooleanArray,
  override val sort: Btor2Sort,
) : Btor2Node(nid, sort) {
  val declsVar = Decls.Var("const_$nid", BvExprs.BvType(sort.width.toInt()))

  override fun getVar(): VarDecl<*>? {
    return declsVar
  }

  override fun getExpr(): Expr<BvType> {
    return declsVar.ref as Expr<BvType>
  }

  override fun <R, P> accept(visitor: Btor2NodeVisitor<R, P>, param: P): R {
    return visitor.visit(this, param)
  }
}
