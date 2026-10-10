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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.SvLibExprTransformer
import hu.bme.mit.theta.frontend.svlib.SvLibTagMetadata
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import java.io.File

class SvLibWitnessWriter : XcfaWitnessWriter {
  override val extension = "svlib"

  override fun writeWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    cexSolverFactory: SolverFactory,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureType?,
    logger: Logger
  ) {
    if (safetyResult.isSafe() && (safetyResult.proof is LocationInvariants)) {
      witnessfile.writeText(toSvLibCorrectnessWitness(safetyResult.proof as LocationInvariants))
    }
  }

  override fun writeTrivialCorrectnessWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureType?
  ) {
    witnessfile.writeText("()\n")
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureType?
  ): String {
    throw UnsupportedOperationException("SV-LIB violation witnesses are not supported")
  }

  private fun toSvLibCorrectnessWitness(proof: LocationInvariants): String {
    val statesByTag: Map<String, MutableList<ExprState>> = proof.partitions.entries
      .fold(LinkedHashMap()) { tagStates, (location, states) ->
        if (states.isNotEmpty()) {
          (location.metadata as? SvLibTagMetadata)?.tags?.forEach { tag ->
            tagStates.getOrPut(tag, { mutableListOf() }).addAll(states)
          }
        }
        tagStates
      }

    val invariantsByTag: Map<String, Expr<BoolType>> = statesByTag
      .mapValues { (_, states) ->
        val invariants = states.map(ExprState::getInvariant)
        ExprUtils.simplify(BoolExprs.Or(invariants))
      }

    val transformer = SvLibExprTransformer()
    val annotations = invariantsByTag.map { (tag, invariant) ->
      """
      (annotate-tag
        ${GenericSmtLibSymbolTable.encodeSymbol(tag)}
        :invariant
      ${transformer.toTerm(invariant).indent()}
      )
      """.trimIndent()
    }

    return "(\n${annotations.joinToString("\n\n").indent(2)}\n)\n"
  }

  private fun String.indent(spaces: Int = 4)
    = this.lineSequence().joinToString("\n") { " ".repeat(spaces) + it }
}
