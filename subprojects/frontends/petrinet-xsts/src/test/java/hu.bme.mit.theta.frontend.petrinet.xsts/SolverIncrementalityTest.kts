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
package hu.bme.mit.theta.frontend.petrinet.xsts

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory

val solverPool = SolverPool(Z3LegacySolverFactory.getInstance())

val x = Decls.Var("x", IntType.getInstance())

val constraint = And(Geq(x.ref, Int(0)), Leq(x.ref, Int(10000)))

val solver = solverPool.requestSolver()

solver.add(PathUtils.unfold(constraint, 0))

for (i in 0..9999) {
  solver.push()
  val negExpr = Neq(x.ref, Int(i))
  solver.add(PathUtils.unfold(negExpr, 0))
  solver.check()
  val model = solver.model
  println(model)
}
