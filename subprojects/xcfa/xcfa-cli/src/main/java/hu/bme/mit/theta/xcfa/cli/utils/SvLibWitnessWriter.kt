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
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.*
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.changeVars
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.io.File
import kotlin.jvm.optionals.getOrElse
import kotlin.jvm.optionals.getOrNull

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
    logger: Logger,
  ) {
    if (safetyResult.isSafe) {
      when (val proof = safetyResult.asSafe().proof) {
        is LocationInvariants ->
          witnessfile.writeText(proof.toSvLibCorrectnessWitness(parseContext))
        is DssInvariants -> witnessfile.writeText(proof.toSvLibCorrectnessWitness(parseContext))
        else ->
          writeTrivialCorrectnessWitness(
            safetyResult,
            inputFile,
            property,
            parseContext,
            witnessfile,
            ltlSpecification,
            architecture,
          )
      }
    } else if (safetyResult.isUnsafe) {
      when (val cex = safetyResult.asUnsafe().cex) {
        is Trace<*, *> -> {
          val concreteTrace =
            SvLibXcfaTraceConcretizer()
              .concretize(
                cex as Trace<XcfaState<PtrState<*>>, XcfaAction>,
                cexSolverFactory,
                parseContext,
              )
          witnessfile.writeText(concreteTrace.toSvLibViolationWitness(parseContext))
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
    architecture: ArchitectureType?,
  ) {
    witnessfile.writeText("()\n")
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureType?,
  ): String {
    throw UnsupportedOperationException("SV-LIB violation witnesses are not supported")
  }
}

private fun LocationInvariants.toSvLibCorrectnessWitness(parseContext: ParseContext) =
  partitions
    .mapValues { (_, states) -> states.map { it.getInvariant() } }
    .toSvLibCorrectnessWitness(parseContext)

private fun DssInvariants.toSvLibCorrectnessWitness(parseContext: ParseContext) =
  invariants
    .mapValues { (_, invariants) -> invariants.orEmpty() }
    .toSvLibCorrectnessWitness(parseContext)

private fun Map<XcfaLocation, List<Expr<BoolType>>>.toSvLibCorrectnessWitness(
  parseContext: ParseContext
): String {
  val passInvariants =
    this.keys.associateWith { location ->
      val invariants =
        parseContext.metadata
          .getMetadataValue(location, "passInvariants")
          .getOrElse {
            parseContext.metadata.getMetadataValue(location.name, "passInvariants").getOrNull()
          }
          ?.let { it as? MutableList<Expr<BoolType>> } ?: emptyList()
      ExprUtils.simplify(BoolExprs.And(invariants))
    }

  val invariantsByTag =
    this.entries.fold(LinkedHashMap<String, MutableList<Expr<BoolType>>>()) {
      invariantsByTag,
      (location, stateInvariants) ->
      val metadata = location.metadata as? SvLibTagMetadata ?: return@fold invariantsByTag
      if (metadata.tags.isNotEmpty() && stateInvariants.isNotEmpty()) {
        val invariants =
          stateInvariants.map { stateInvariant ->
            ExprUtils.simplify(BoolExprs.And(listOf(stateInvariant) + passInvariants[location]))
              .projectToScope(metadata.procedure, parseContext)
          }
        metadata.tags.forEach {
          invariantsByTag.getOrPut(it) { mutableListOf() }.addAll(invariants)
        }
      }
      invariantsByTag
    }

  return invariantsByTag
    .mapValues { (_, invariants) -> ExprUtils.simplify(BoolExprs.Or(invariants)) }
    .toSvLibCorrectnessWitness()
}

/** Existentially quantifies the variables not in scope in [procedure]. */
private fun Expr<BoolType>.projectToScope(
  procedure: String?,
  parseContext: ParseContext,
): Expr<BoolType> {
  val metadata = parseContext.metadata
  val outOfScope =
    ExprUtils.getVars(this).filterNot {
      val declaredIn = metadata.getMetadataValue(it, "declaredIn").getOrNull()
      declaredIn == GLOBAL_SCOPE || (procedure != null && declaredIn == procedure)
    }
  if (outOfScope.isEmpty()) return this

  val params = outOfScope.associateWith { v -> Decls.Param("${v.name}__proj", v.type) }
  val quantified = BoolExprs.Exists(params.values, ExprUtils.changeDecls(this, params))
  return ExprUtils.simplify(quantified)
}

private fun Map<String, Expr<BoolType>>.toSvLibCorrectnessWitness(): String {
  val annotations =
    this.map { (tag, invariant) ->
      """
      (annotate-tag
        ${GenericSmtLibSymbolTable.encodeSymbol(tag)}
        :invariant
      ${SvLibExprTransformer().toTerm(invariant).indent()}
      )
      """
        .trimIndent()
    }

  return "(\n${annotations.joinToString("\n\n").indent(2)}\n)\n"
}

private fun Trace<XcfaState<ExplState>, XcfaAction>.toSvLibViolationWitness(
  parseContext: ParseContext
): String {
  val initState = this.states.firstOrNull() ?: throw IllegalStateException("empty trace")
  val xcfa = initState.xcfa ?: throw IllegalStateException("no XCFA associated with trace")

  val initVal = initState.sGlobal.getVal()
  val globalVarMap =
    initVal.toMap().filter { (varDecl, _) -> varDecl in xcfa.globalVars.map { it.wrappedVar } }
  val model = SmtLibModel(emptyMap()) // TODO extract function definitions from trace model

  val entryProcedure =
    xcfa.initProcedures.firstOrNull()?.first ?: throw IllegalStateException("no entry procedure")

  var property: String? = null
  val steps =
    states.drop(1).zip(actions).mapNotNull { (nextState, action) ->
      val labels = action.label.getFlatLabels()
      val metadata =
        labels.firstOrNull()?.metadata as? SvLibWitnessMetadata ?: return@mapNotNull null
      when (metadata) {
        is SvLibWitnessMetadata.InitProcVars -> {
          val procedure =
            xcfa.procedures.find { it.name == metadata.procedure }
              ?: throw IllegalStateException("call to unknown procedure")
          InitProcVarsStep(
            procedure,
            nextState.sGlobal.getVal().filterLocal(procedure, parseContext),
          )
        }
        is SvLibWitnessMetadata.Havoc -> {
          val values =
            metadata.vars.mapNotNull { varDecl ->
              nextState.sGlobal.getVal().eval(varDecl).getOrNull()?.let { varDecl to it }
            }
          HavocStep(ImmutableValuation.from(values.toMap()))
        }
        is SvLibWitnessMetadata.Choice -> ChoiceStep(metadata.index)
        is SvLibWitnessMetadata.Annotation -> {
          property = "${metadata.tag ?: ""} ${metadata.property}"
          null
        }
      }
    }

  val witness =
    SvLibViolationWitness(
      model,
      ImmutableValuation.from(globalVarMap),
      entryProcedure,
      steps,
      property ?: throw IllegalStateException("no property violation found"),
    )
  return witness.toString()
}

class SvLibXcfaTraceConcretizer : XcfaTraceConcretizer() {
  override fun isProgramVar(decl: VarDecl<*>, parseContext: ParseContext?) =
    !decl.name.startsWith(tmpVarPrefix)

  // labels with the same metadata object belong to the same SV-LIB statement
  override fun isSbe(label: XcfaLabel, other: XcfaLabel) =
    label.metadata === other.metadata && !label.isWitnessStep()

  override fun concreteState(
    state: XcfaState<*>,
    valuation: Valuation,
    varSoFar: Set<VarDecl<*>>,
    nondetVars: Set<VarDecl<*>>,
    parseContext: ParseContext,
  ): ExplState {
    val currentState = state.processes.values.first()
    val varLookup = currentState.varLookup.firstOrNull()?.reverseMapping() ?: emptyMap()
    return ExplState.of(valuation.changeVars(varLookup, keepAll = true))
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
        (steps${if (steps.isEmpty()) "" else "\n" + steps.joinToString("\n" ) { "          $it" }})
        (incorrect-annotation $violatedProperty)
      ))
    """
      .trimIndent()
  }
}

private sealed class SvLibViolationWitnessStep

private data class InitProcVarsStep(val procedure: XcfaProcedure, val arguments: Valuation) :
  SvLibViolationWitnessStep() {

  override fun toString() = "(init-proc-vars ${procedure.name} ${arguments.toSvLib()})"
}

private data class HavocStep(val values: Valuation) : SvLibViolationWitnessStep() {

  override fun toString() = "(havoc ${values.toSvLib()})"
}

private data class ChoiceStep(val branchIndex: Int) : SvLibViolationWitnessStep() {

  override fun toString() = "(choice $branchIndex)"
}

private data class LeapStep(val tag: String, val valuation: Valuation) :
  SvLibViolationWitnessStep() {

  override fun toString() =
    "(leap ${GenericSmtLibSymbolTable.encodeSymbol(tag)} ${valuation.toSvLib()})"
}

private fun Valuation.toSvLib(): String {
  if (this.toMap().isEmpty()) return ""
  val transformer = SvLibExprTransformer()
  return toMap().entries.joinToString(" ") { (varDecl, litExpr) ->
    "(${GenericSmtLibSymbolTable.encodeSymbol(varDecl.name)} ${transformer.toTerm(litExpr)})"
  }
}

private fun Valuation.filterLocal(procedure: XcfaProcedure, parseContext: ParseContext) =
  this.toMap()
    .filterKeys { varDecl ->
      procedure.name ==
        parseContext.metadata.getMetadataValue(varDecl, "declaredIn")?.getOrNull() &&
        procedure.params.all { (param, dir) -> param != varDecl || dir != ParamDirection.IN }
    }
    .let(ImmutableValuation::from)

private fun String.indent(spaces: Int = 4) =
  this.lineSequence().joinToString("\n") { " ".repeat(spaces) + it }
