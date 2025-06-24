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
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.decl.Decls.Param
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.chc.ChcMetadata
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLocation

fun writeModel(xcfa: XCFA, safetyResult: SafetyResult<*, *>): String {
  // we write sat/unsat first, then the model, if applicable
  val sb = StringBuilder()
  if (safetyResult.isUnsafe) {
    sb.appendLine("unsat")
  } else {
    sb.appendLine("sat")
    val solver = Z3SolverFactory.getInstance().createSolver()
    val proof = safetyResult.asSafe().proof
    val needsModel =
      xcfa.procedures.flatMap { it.locs }.filter { it.metadata is ChcMetadata }.toMutableSet()
    if (proof is LocationInvariants) {
      sb.appendLine("(")
      if (needsModel.isEmpty())
        sb.appendLine(
          "; No model found. Currently, the backwards transformation does not produce models -- if possible, use the default forward transformation."
        )
      for ((loc, inv) in proof.partitions) {
        if (loc.metadata is ChcMetadata) {
          needsModel.remove(loc)
          sb.appendLine(writeFun(loc, solver, inv))
        }
      }
      for (loc in needsModel) {
        sb.appendLine(writeFun(loc, solver))
      }
      sb.appendLine(")")
    }
  }
  return sb.toString()
}

private fun writeFun(
  loc: XcfaLocation,
  solver: Solver,
  inv: Collection<ExprState> = emptySet(),
): String {
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
        .let { if (metadata.isBackwards) Not(it) else it }
    )

  val decls =
    params.values.joinToString(" ") { "(${manager.toSymbol(it)} ${manager.toSort(it.type)})" }

  return "   (define-fun |${metadata.name}| (${decls}) Bool ${manager.toTerm(expr)})"
}

fun getDef(inv: ExplState, params: Map<VarDecl<*>, ConstDecl<*>>): Expr<BoolType> {
  if (inv.isBottom) return False()
  val notIncludedParams = inv.toMap().filter { !params.containsKey(it.key) }
  val expr =
    if (notIncludedParams.isNotEmpty()) {
      val existParams = notIncludedParams.keys.associateWith { Param(it.name, it.type) }
      Exists(
        existParams.values,
        And(inv.toMap().map { Eq(params[it.key]?.ref ?: existParams[it.key]!!.ref, it.value) }),
      )
    } else {
      And(inv.toMap().map { Eq(params[it.key]!!.ref, it.value) })
    }
  return expr
}

fun getDef(inv: PredState, params: Map<VarDecl<*>, ConstDecl<*>>): Expr<BoolType> {
  if (inv.isBottom) return False()
  val expr = ExprUtils.changeDecls(inv.toExpr(), params)
  val varsNotParams = ExprUtils.getVars(expr).associateWith { Param(it.name, it.type) }

  return if (varsNotParams.isNotEmpty()) {
    Exists(varsNotParams.values, ExprUtils.changeDecls(expr, varsNotParams))
  } else {
    expr
  }
}
