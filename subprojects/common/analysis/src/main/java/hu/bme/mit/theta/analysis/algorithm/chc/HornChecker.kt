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
package hu.bme.mit.theta.analysis.algorithm.chc

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.Relation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.solver.ProofNode
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.SolverStatus

data class Invariant(val lookup: Map<Relation, Expr<BoolType>>) : Proof

data class CexTree(val proofNode: ProofNode) : Cex {

  override fun length(): Int = proofNode.depth()
}

/** A checker for CHC-based verification. */
class HornChecker(
  private val relations: List<Relation>,
  private val hornSolverFactory: SolverFactory,
) : SafetyChecker<Invariant, CexTree, UnitPrec> {

  override fun check(prec: UnitPrec?): SafetyResult<Invariant, CexTree> {
    val solver = hornSolverFactory.createHornSolver()
    Logger.mainStep("Starting encoding\n")
    solver.add(relations)
    Logger.detail(
      "Relations:\n\t${
            relations.joinToString("\n\t") {
                it.constDecl.toString()
            }
        }\n",
    )
    Logger.detail(
      "Rules:\n\t${
            solver.assertions.joinToString("\n\t") {
                it.toString().replace(Regex("[\r\n\t ]+"), " ")
            }
        }\n",
    )
    Logger.mainStep("Added constraints to solver\n")
    solver.check()
    Logger.mainStep("Check() finished (result: ${solver.status})\n")
    return when (solver.status) {
      SolverStatus.SAT -> {
        Logger.mainStep("Proof (model) found\n")
        val model = solver.model.toMap()
        SafetyResult.safe(
          Invariant(relations.associateWith { model[it.constDecl] as? Expr<BoolType> ?: True() })
        )
      }

      SolverStatus.UNSAT -> {
        Logger.mainStep("Counterexample found\n")
        val proof = solver.proof
        SafetyResult.unsafe(CexTree(proof), Invariant(emptyMap()))
      }

      else -> {
        Logger.mainStep("No solution found.\n")
        SafetyResult.unknown()
      }
    }
  }
}
