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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.SvLibExprTransformer
import hu.bme.mit.theta.frontend.svlib.SvLibSourceMetadata
import hu.bme.mit.theta.frontend.svlib.SvLibTagMetadata
import hu.bme.mit.theta.frontend.svlib.tmpVarPrefix
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
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
    if (safetyResult.isSafe) {
      when (val proof = safetyResult.asSafe().proof) {
        is LocationInvariants -> witnessfile.writeText(proof.toSvLibCorrectnessWitness())
        else -> writeTrivialCorrectnessWitness(safetyResult, inputFile, property, parseContext, witnessfile, ltlSpecification, architecture)
      }
    } else if (safetyResult.isUnsafe) {
      when (val cex = safetyResult.asUnsafe().cex) {
        is Trace<*, *>  -> {
          val concreteTrace = SvLibXcfaTraceConcretizer().concretize(
            cex as Trace<XcfaState<PtrState<*>>, XcfaAction>,
            cexSolverFactory,
            parseContext,
            wrapExprTraceCheckerWithDataRaceCondition(property, parseContext),
          )
          witnessfile.writeText(concreteTrace.toSvLibViolationWitness())
        }
        else -> generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
      }
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

  private fun LocationInvariants.toSvLibCorrectnessWitness(): String {
    val statesByTag: Map<String, MutableList<ExprState>> = this.partitions.entries
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

private fun Trace<XcfaState<ExplState>, XcfaAction>.toSvLibViolationWitness(): String {
  val initState = this.states.firstOrNull() ?: throw IllegalStateException("empty trace")
  val xcfa = initState.xcfa ?: throw IllegalStateException("no XCFA associated with trace")

  val initVal = initState.sGlobal.getVal()
  val globalVarMap = initVal.toMap()
    .filter { (varDecl, _) -> varDecl in xcfa.globalVars.map { it.wrappedVar } }
  val model = SmtLibModel(globalVarMap.map { (varDecl, expr) -> varDecl.name to expr.toString() }.toMap())

  val entryProcedure = xcfa.initProcedures.firstOrNull()?.first ?: throw IllegalStateException("no entry procedure")
  val property = actions.flatMap { it.label.getFlatLabels() }.mapNotNull { (it.metadata as? SvLibSourceMetadata)?.source }
    .findLast { it.contains(":check-true") } ?: throw IllegalStateException("no property violation found")


  var currentProcedure: XcfaProcedure = entryProcedure
  val steps = states.zipWithNext().zip(actions).flatMap { (states, action) ->
    val (prevExplState, newExplState) = states
    val prevState = prevExplState.processes.values.first() // no concurrency in SV-LIB
    val newState = newExplState.processes.values.first()   // no concurrency in SV-LIB

    val steps = mutableListOf<SvLibViolationWitnessStep>()
    action.label.getFlatLabels().forEach { label ->
      when (label) {
        is InvokeLabel -> {
          currentProcedure = xcfa.procedures.find { label.name == it.name }
            ?: throw IllegalStateException("call to unknown procedure")
        }
        is StmtLabel -> {
          val stmt = label.stmt
          (action.edge.metadata as? SvLibSourceMetadata)?.source?.let { metadata ->
            Regex("choice (\\d+)").find(metadata)?.groups?.get(1)?.value?.let { index ->
              steps.add(ChoiceStep(index.toInt()))
            }
          }
          (label.metadata as? SvLibSourceMetadata)?.source?.let { metadata ->
            Regex("call (\\S+) \\(").find(metadata)?.groups?.get(1)?.value?.let { procedureName ->
              currentProcedure = xcfa.procedures.find { procedureName == it.name }
                ?: throw IllegalStateException("call to unknown procedure")
              steps.add(InitProcVarsStep(currentProcedure, newExplState.sGlobal.getVal()))
            }
          }
          if (stmt is HavocStmt<*>) {
            newExplState.sGlobal.getVal().toMap()[stmt.varDecl]?.let { value ->
              val varDecl = prevState.varLookup[0].reverseMapping()[stmt.varDecl] ?: stmt.varDecl
              steps.add(HavocStep(varDecl, value))
            }
          }
        }
        else -> {}
      }
    }

    if (!prevState.paramsInitialized && newState.paramsInitialized) {
      steps.addFirst(InitProcVarsStep(currentProcedure, newExplState.sGlobal.getVal()))
    }

    steps
  }

  val witness = SvLibViolationWitness(
    model,
    ImmutableValuation.from(globalVarMap),
    entryProcedure,
    steps,
    property
  )
  return witness.toString()
}

class SvLibXcfaTraceConcretizer : XcfaTraceConcretizer() {
  override fun isProgramVar(decl: VarDecl<*>, parseContext: ParseContext?) = !decl.name.startsWith(tmpVarPrefix)

  override fun isSbe(label: XcfaLabel) = true // doesn't matter for SV-LIB witness

  override fun concreteState(
    state: XcfaState<*>, valuation: Valuation, varSoFar: Set<VarDecl<*>>, nondetVars: Set<VarDecl<*>>,
    parseContext: ParseContext
  ): ExplState {
    val currentState = state.processes.values.first()
    val currentLoc = currentState.locs.peek() // no concurrency in SV-LIB
    val xcfa = state.xcfa ?: throw IllegalStateException("no XCFA associated with trace")
    val currentProcedure = xcfa.procedures.find { currentLoc in it.locs }
      ?: throw IllegalStateException("no procedure associated with trace")
    val globalVars = xcfa.globalVars.map(XcfaGlobalVar::wrappedVar)

    val genericValuationMap: Map<Decl<*>, LitExpr<*>> = valuation
      .changeVars(globalVars.associateWith { it } + currentState.varLookup[0].reverseMapping()).toMap()
      .filterKeys { varDecl ->
        (varDecl in currentProcedure.vars || varDecl in globalVars) && currentProcedure.params.all { (param, dir) ->
          param != varDecl || dir != ParamDirection.IN
        }
      }

    return ExplState.of(ImmutableValuation.from(genericValuationMap))
  }
}

private data class SvLibViolationWitness(
  val model: SmtLibModel,
  val globalVarValuation: Valuation,
  val entryProcedure: XcfaProcedure,
  val steps: List<SvLibViolationWitnessStep>,
  val violatedProperty: String,
) {
  override fun toString(): String {
    return """
      ((select-trace 
        (model ${if (model.decls.isEmpty()) "" else "$model"})
        (init-global-vars ${globalVarValuation.toSvLib()})
        (entry-proc ${entryProcedure.name})
        (steps${if (steps.isEmpty()) "" else "\n" + steps.joinToString("\n", ) { "          $it" }})
        (incorrect-annotation $violatedProperty)
      ))
    """.trimIndent()
  }
}

private sealed class SvLibViolationWitnessStep

private data class InitProcVarsStep(
  val procedure: XcfaProcedure,
  val arguments: Valuation,
) : SvLibViolationWitnessStep() {

  override fun toString()
    = "(init-proc-vars ${procedure.name} ${arguments.toSvLib()})"
}

private data class HavocStep(
  val varDecl: VarDecl<*>,
  val value: LitExpr<*>,
) : SvLibViolationWitnessStep() {

  override fun toString()
    = "(havoc (${GenericSmtLibSymbolTable.encodeSymbol(varDecl.name)} ${SvLibExprTransformer().toTerm(value)}))"
}

private data class ChoiceStep(
  val branchIndex: Int,
) : SvLibViolationWitnessStep() {

  override fun toString() = "(choice $branchIndex)"
}

private data class LeapStep(
  val tag: String,
  val valuation: Valuation,
) : SvLibViolationWitnessStep() {

  override fun toString() = "(leap ${GenericSmtLibSymbolTable.encodeSymbol(tag)} ${valuation.toSvLib()})"
}

private fun Valuation.toSvLib(): String {
  if (this.toMap().isEmpty()) return ""
  val transformer = SvLibExprTransformer()
  return toMap().entries.joinToString(" ") { (varDecl, litExpr) ->
    "(${GenericSmtLibSymbolTable.encodeSymbol(varDecl.name)} ${transformer.toTerm(litExpr)})"
  }
}
