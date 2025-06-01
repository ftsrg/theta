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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.chc.ChcMetadata
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.z3.Z3SolverFactory

fun writeModel(safetyResult: SafetyResult<*, *>) {
  // we write sat/unsat first, then the model, if applicable
  if (safetyResult.isUnsafe) {
    println("unsat")
  } else {
    println("sat")
    val solver = Z3SolverFactory.getInstance().createSolver()
    val proof = safetyResult.asSafe().proof
    if (proof is LocationInvariants) {
      println("(")
      for ((loc, inv) in proof.partitions) {
        if (loc.metadata is ChcMetadata) {

          val metadata = loc.metadata as ChcMetadata
          val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())

          val params = metadata.varDecls.associateWith { Const(it.name, it.type) }

          val expr =
            solver.simplify(
              Or(
                inv.map {
                  when (it) {
                    is ExplState -> getDef(it, params)
                    is PredState -> getDef(it, params)
                    else -> error("Unknown state type: $it")
                  }
                }
              )
            )

          val decls =
            params.values
              .map { "(${manager.toSymbol(it)} ${manager.toSort(it.type)})" }
              .joinToString(" ")

          println("   (define-fun ${metadata.name} (${decls}) Bool ${manager.toTerm(expr)})")
        }
      }
      println(")")
    }
  }
}

fun getDef(inv: ExplState, params: Map<VarDecl<*>, ConstDecl<*>>): Expr<BoolType> {
  val expr =
    And(inv.toMap().filter { params[it.key] != null }.map { Eq(params[it.key]!!.ref, it.value) })
  return expr
}

fun getDef(inv: PredState, params: Map<VarDecl<*>, ConstDecl<*>>): Expr<BoolType> {
  val expr = ExprUtils.changeDecls(inv.toExpr(), params)
  val varsNotParams = ExprUtils.getVars(expr).associateWith { Param(it.name, it.type) }

  return if (varsNotParams.isNotEmpty()) {
    Exists(varsNotParams.values, ExprUtils.changeDecls(expr, varsNotParams))
  } else {
    expr
  }
}
