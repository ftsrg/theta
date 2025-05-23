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
import hu.bme.mit.theta.core.decl.Decls.Const
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.chc.ChcMetadata
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager

fun writeModel(safetyResult: SafetyResult<*, *>) {
  // we write sat/unsat first, then the model, if applicable
  if (safetyResult.isUnsafe) {
    println("unsat")
  } else {
    println("sat")
    val proof = safetyResult.asSafe().proof
    if (proof is LocationInvariants) {
      for ((loc, inv) in proof.partitions) {
        if (loc.metadata is ChcMetadata) {

          val metadata = loc.metadata as ChcMetadata
          val manager = GenericSmtLibTransformationManager(GenericSmtLibSymbolTable())
          val allVars = ExprUtils.getVars(inv).toSet()
          val paramVars = metadata.varDecls

          val canSimplify =
            inv is OrExpr &&
              inv.ops.all {
                it is AndExpr &&
                  it.ops.all {
                    it is EqExpr<*> && it.leftOp is RefExpr<*> && it.rightOp is LitExpr<*>
                  }
              }

          val simplifiedInv =
            if (canSimplify) {
              Or(
                inv.ops.map {
                  And(
                    it.ops
                      .filter { ((it as EqExpr<*>).leftOp as RefExpr<*>).decl in paramVars }
                      .toList() as List<Expr<BoolType>>
                  )
                }
              )
            } else {
              inv
            }
          val varToConst = allVars.associateWith { Const(it.name, it.type) }
          val decls = paramVars.joinToString(" ") { "(${it.name} ${manager.toSort(it.type)})" }
          println(
            "(define-fun ${metadata.name} (${decls}) Bool (${manager.toTerm(ExprUtils.changeDecls(simplifiedInv, varToConst))}))"
          )
        }
      }
    }
  }
}
