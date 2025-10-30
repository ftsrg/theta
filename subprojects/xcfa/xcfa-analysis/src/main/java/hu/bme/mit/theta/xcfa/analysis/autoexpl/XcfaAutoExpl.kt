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
package hu.bme.mit.theta.xcfa.analysis.autoexpl

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewOperandsAutoExpl
import hu.bme.mit.theta.common.container.Containers
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.utils.collectAssumes

fun xcfaNewOperandsAutoExpl(xcfa: XCFA): AutoExpl {
  val atoms =
    xcfa.collectAssumes().flatMap { ExprUtils.getAtoms(it) }.map { ExprUtils.canonize(it) }.toSet()

  val declToOps = Containers.createMap<Decl<*>, MutableSet<Expr<*>>>()
  atoms
    .map { if (it is NotExpr) it.op else it }
    .filter { it.getOps().size > 1 }
    .forEach { atom ->
      atom.ops.filterIsInstance<RefExpr<*>>().forEach { refExpr ->
        atom.ops
          .filterNot { refExpr == it }
          .forEach { op ->
            declToOps.computeIfAbsent(refExpr.getDecl()) { Containers.createSet() }!!.add((op))
          }
      }
    }
  return NewOperandsAutoExpl(setOf(), declToOps, 0)
}
