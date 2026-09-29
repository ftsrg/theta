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
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.SvLibMetadata
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XcfaLocation
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
    witnessfile.writeText(emptyWitness())
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureType?
  ): String {
    throw UnsupportedOperationException("SV-LIB violation witnesses are not supported")
  }

  private fun toSvLibCorrectnessWitness(proof: LocationInvariants): String {
    val invariantsByTag: Map<String, Expr<BoolType>> = locationInvariantsByTag(proof)
    if (invariantsByTag.isEmpty()) {
      return emptyWitness()
    }

    val transformer = SvLibTermTransformer(invariantsByTag.values)
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

  private fun locationInvariantsByTag(proof: LocationInvariants): Map<String, Expr<BoolType>> {
    val invariantsByTag: MutableMap<String, MutableList<Expr<BoolType>>> = LinkedHashMap()

    for ((location, states) in proof.getPartitions()) {
      val tag = svLibTag(location)
      if (tag == null || states.isEmpty()) continue

      val invariant = ExprUtils.simplify(BoolExprs.Or(states.map(ExprState::getInvariant)))
      invariantsByTag.getOrPut(tag) { mutableListOf() }.add(invariant)
    }

    return invariantsByTag.mapValues { (_, invariants) ->
      ExprUtils.simplify(BoolExprs.Or(invariants))
    }
  }

  private fun svLibTag(location: XcfaLocation) = (location.metadata as? SvLibMetadata)?.tag

  private fun String.indent(spaces: Int = 4)
    = this.lineSequence().joinToString("\n") { " ".repeat(spaces) + it }


  private fun emptyWitness() = "()\n"
}

private class SvLibTermTransformer(expressions: Collection<Expr<BoolType>>) {
  private val symbolTable = GenericSmtLibSymbolTable()
  private val transformationManager = GenericSmtLibTransformationManager(symbolTable)
  private val variableConstants: MutableMap<VarDecl<*>, ConstDecl<*>> = LinkedHashMap()

  init {
    expressions.forEach { expr -> this.registerVariables(expr) }
  }

  fun toTerm(expr: Expr<BoolType>): String {
    registerVariables(expr)
    val printableExpr = ExprUtils.changeDecls(expr, variableConstants)
    return transformationManager.toTerm(printableExpr)
  }

  fun registerVariables(expr: Expr<*>) {
    for (varDecl in ExprUtils.getVars(expr)) {
      if (variableConstants.containsKey(varDecl)) continue

      val constDecl = Decls.Const(varDecl.name, varDecl.type)
      transformConst(constDecl)
      variableConstants.putIfAbsent(varDecl, constDecl)
    }
  }

  private fun transformConst(decl: ConstDecl<*>) {
    val (paramTypes, returnType) = extractTypes(decl.type)

    val returnSort = transformationManager.toSort(returnType)
    val paramSorts = paramTypes.map(transformationManager::toSort)

    val symbolName = GenericSmtLibSymbolTable.encodeSymbol(decl.name)
    val symbolDeclaration = "(declare-fun $symbolName (${paramSorts.joinToString(" ")}) $returnSort)"
    symbolTable.put(decl, symbolName, symbolDeclaration)
  }

  private fun extractTypes(type: Type): Pair<List<Type>, Type> {
    if (type is FuncType<*, *>) {
      val paramType = type.getParamType()
      val resultType = type.getResultType()

      check(paramType !is FuncType<*, *>)

      val (paramTypes, newResultType) = extractTypes(resultType)
      val newParamTypes = listOf(paramType) + paramTypes
      return Pair(newParamTypes, newResultType)
    } else {
      return Pair(emptyList(), type)
    }
  }
}
