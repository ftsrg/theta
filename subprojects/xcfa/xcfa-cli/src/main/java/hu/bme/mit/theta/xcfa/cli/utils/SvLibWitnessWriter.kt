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
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.*
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncLitExpr
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.svlib.*
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.changeVars
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.analysis.reverseMapping
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.passes.removedLocations
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
          val (concreteTrace, constants) =
            SvLibXcfaTraceConcretizer()
              .concretizeWithModel(
                cex as Trace<XcfaState<PtrState<*>>, XcfaAction>,
                cexSolverFactory,
                parseContext,
              )
          witnessfile.writeText(concreteTrace.toSvLibViolationWitness(constants, parseContext))
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
  ) = "()\n"
}

private fun LocationInvariants.toSvLibCorrectnessWitness(parseContext: ParseContext) =
  partitions
    .mapValues { (_, states) -> states.map { it.getInvariant() } }
    .toSvLibCorrectnessWitness(parseContext)

private fun DssInvariants.toSvLibCorrectnessWitness(parseContext: ParseContext) =
  invariants.toSvLibCorrectnessWitness(parseContext)

/** Maps each location to the states reaching it: none if it is unreachable, null if unknown. */
private fun Map<XcfaLocation, List<Expr<BoolType>>?>.toSvLibCorrectnessWitness(
  parseContext: ParseContext
): String {
  val passInvariants =
    this.keys.associateWith { location ->
      parseContext.metadata
        .getMetadataValue(location, "passInvariants")
        .getOrElse {
          parseContext.metadata.getMetadataValue(location.name, "passInvariants").getOrNull()
        }
        ?.let { ExprUtils.simplify(BoolExprs.And(it as? MutableList<Expr<BoolType>>)) }
    }

  val locationInvariants =
    this.map { (location, stateInvariants) ->
      val reached =
        stateInvariants?.let { if (it.isEmpty()) BoolExprs.False() else BoolExprs.Or(it) }
      location to
        ExprUtils.simplify(BoolExprs.And(listOfNotNull(reached, passInvariants[location])))
    } + parseContext.removedLocations() // locations removed by passes still matter for tags

  val exits =
    locationInvariants
      .mapNotNull { (location, _) -> location.metadata as? SvLibProcedureExit }
      .associateBy { it.procedure }
  val annotations = LinkedHashMap<String, SvLibTagAnnotation>()
  fun annotate(
    tags: Set<String>,
    invariant: Expr<BoolType>,
    scope: Set<VarDecl<*>>,
    attribute: (SvLibTagAnnotation) -> MutableList<Expr<BoolType>>,
  ) {
    if (tags.isEmpty()) return
    val projectedInvariant = ExprUtils.simplify(invariant.projectToScope(scope, parseContext))
    tags.forEach {
      attribute(annotations.getOrPut(it, ::SvLibTagAnnotation)).add(projectedInvariant)
    }
  }

  for ((location, invariant) in locationInvariants) {
    when (val metadata = location.metadata) {
      is SvLibTagMetadata -> {
        annotate(metadata.tags, invariant, metadata.liveVars) { it.invariants }
        val exit = exits[metadata.procedure] ?: continue
        annotate(metadata.tags intersect exit.tags, invariant, exit.inputs) { it.requires }
      }
      is SvLibProcedureExit ->
        annotate(metadata.tags, invariant, metadata.inputs + metadata.outputs) { it.ensures }
    }
  }

  return annotations.toSvLibCorrectnessWitness()
}

/**
 * The invariants of the occurrences of a tag, and of their starts and ends if it has a contract.
 */
private class SvLibTagAnnotation {
  val invariants = mutableListOf<Expr<BoolType>>()
  val requires = mutableListOf<Expr<BoolType>>()
  val ensures = mutableListOf<Expr<BoolType>>()
}

/** Existentially quantifies the variables that are neither global nor in [scope]. */
private fun Expr<BoolType>.projectToScope(
  scope: Set<VarDecl<*>>,
  parseContext: ParseContext,
): Expr<BoolType> {
  val outOfScope =
    ExprUtils.getVars(this).filterNot {
      it in scope || parseContext.metadata.getMetadataValue(it, "isGlobal").getOrNull() == true
    }
  if (outOfScope.isEmpty()) return this

  val params =
    outOfScope
      .mapIndexed { i, v ->
        val name =
          "${v.name}__proj_$i".let { if (it.contains('|')) "|${it.replace("|", "")}|" else it }
        v to Decls.Param(name, v.type)
      }
      .toMap()
  val quantified = BoolExprs.Exists(params.values, ExprUtils.changeDecls(this, params))
  return ExprUtils.simplify(quantified)
}

private fun Map<String, SvLibTagAnnotation>.toSvLibCorrectnessWitness(): String {
  val annotations =
    this.map { (tag, annotation) ->
      val attributes =
        listOf(
            ":invariant" to annotation.invariants,
            ":requires" to annotation.requires,
            ":ensures" to annotation.ensures,
          )
          .filter { (_, invariants) -> invariants.isNotEmpty() }
          .joinToString("\n") { (keyword, invariants) ->
            val invariant = ExprUtils.simplify(BoolExprs.Or(invariants))
            "$keyword\n${SvLibExprTransformer().toTerm(invariant).indent(2)}"
          }
      "(annotate-tag\n  ${GenericSmtLibSymbolTable.encodeSymbol(tag)}\n${attributes.indent(2)}\n)"
    }

  return "(\n${annotations.joinToString("\n\n").indent(2)}\n)\n"
}

private fun Trace<XcfaState<ExplState>, XcfaAction>.toSvLibViolationWitness(
  constants: Valuation,
  parseContext: ParseContext,
): String {
  val initState = this.states.firstOrNull() ?: throw IllegalStateException("empty trace")
  val xcfa = initState.xcfa ?: throw IllegalStateException("no XCFA associated with trace")

  val initVal = initState.sGlobal.getVal()
  val modelSymbols =
    parseContext.metadata.getMetadataValue(MODEL_SYMBOLS, "modelSymbols").getOrNull()
      as? List<Decl<*>> ?: emptyList()
  val globalVarMap =
    initVal.toMap().filter { (varDecl, _) ->
      varDecl in xcfa.globalVars.map { it.wrappedVar } && varDecl !in modelSymbols
    }
  val model =
    modelSymbols.map {
      it.defineWith(initVal.eval(it).getOrNull() ?: constants.eval(it).getOrNull())
    }

  var property: String? = null
  val steps =
    states.drop(1).zip(actions).mapNotNull { (nextState, action) ->
      val labels = action.label.getFlatLabels()
      val metadata =
        labels.firstOrNull()?.metadata as? SvLibWitnessMetadata ?: return@mapNotNull null
      when (metadata) {
        is SvLibWitnessMetadata.InitProcVars -> {
          val values = nextState.sGlobal.getVal().toMap().filterKeys { it in metadata.initVars }
          InitProcVarsStep(metadata.procedure, ImmutableValuation.from(values))
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

  // the verified procedure is called by a wrapper, so its body is the first one entered
  val entryProcedure =
    steps.filterIsInstance<InitProcVarsStep>().firstOrNull()?.procedure
      ?: throw IllegalStateException("no entry procedure")

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

  /** Also returns the values of the uninterpreted constants and functions used by the trace. */
  fun concretizeWithModel(
    trace: Trace<XcfaState<PtrState<*>>, XcfaAction>,
    solverFactory: SolverFactory,
    parseContext: ParseContext,
  ): Pair<Trace<XcfaState<ExplState>, XcfaAction>, Valuation> {
    val checker = ModelKeepingTraceChecker(solverFactory.createSolver())
    return concretize(trace, solverFactory, parseContext) { checker } to checker.constants
  }
}

/**
 * Checks the feasibility of a trace without interpolation, and keeps the values of the constants
 * from the same model as the states, so that they are consistent.
 */
private class ModelKeepingTraceChecker(private val solver: Solver) :
  ExprTraceChecker<ItpRefutation> {
  var constants: Valuation = ImmutableValuation.empty()
    private set

  override fun check(trace: Trace<out ExprState, out ExprAction>): ExprTraceStatus<ItpRefutation> {
    val indexings = mutableListOf(VarIndexingFactory.indexing(0))
    solver.add(PathUtils.unfold(trace.getState(0).toExpr(), indexings[0]))
    for (i in 1 until trace.states.size) {
      indexings += indexings[i - 1].add(trace.getAction(i - 1).nextIndexing())
      solver.add(PathUtils.unfold(trace.getState(i).toExpr(), indexings[i]))
      solver.add(PathUtils.unfold(trace.getAction(i - 1).toExpr(), indexings[i - 1]))
    }
    check(solver.check().isSat) { "Infeasible trace." }

    val model = solver.model
    constants =
      ImmutableValuation.from(
        model.decls
          .filter { it is ConstDecl<*> && it !is IndexedConstDecl<*> }
          .mapNotNull { decl -> model.eval(decl).getOrNull()?.let { decl to it } }
          .toMap()
      )
    val valuations = indexings.map { PathUtils.extractValuation(model, it) }
    return ExprTraceStatus.feasible(Trace.of(valuations, trace.actions))
  }
}

/** The model definition of this constant or function, with a default value if it has none. */
private fun Decl<*>.defineWith(value: LitExpr<*>?): String {
  val transformer = SvLibExprTransformer()
  val params = mutableListOf<VarDecl<*>>()
  var type = this.type
  var body: Expr<*>? = value
  while (type is FuncType<*, *>) {
    val param = Decls.Var("x${params.size}", type.paramType)
    params += param
    body =
      when (body) {
        null -> null
        is FuncLitExpr<*, *> -> ExprUtils.changeDecls(body.result, mapOf(body.param to param))
        else -> throw IllegalStateException("Unexpected value of '$name': $value")
      }
    type = type.resultType
  }
  val paramList = params.joinToString(" ") { "(${it.name} ${transformer.toSort(it.type)})" }
  val term = transformer.toTerm(body ?: TypeUtils.getDefaultValue(type))
  val symbol = GenericSmtLibSymbolTable.encodeSymbol(name)
  return "(define-fun $symbol ($paramList) ${transformer.toSort(type)} $term)"
}

private data class SvLibViolationWitness(
  val model: List<String>,
  val globalVarValuation: Valuation,
  val entryProcedure: String,
  val steps: List<SvLibViolationWitnessStep>,
  val violatedProperty: String,
) {
  override fun toString(): String {
    return """
      ((select-trace 
        (model${if (model.isEmpty()) "" else "\n" + model.joinToString("\n") { "          $it" }})
        (init-global-vars ${globalVarValuation.toSvLib()})
        (entry-proc $entryProcedure)
        (steps${if (steps.isEmpty()) "" else "\n" + steps.joinToString("\n" ) { "          $it" }})
        (incorrect-annotation $violatedProperty)
      ))
    """
      .trimIndent()
  }
}

private sealed class SvLibViolationWitnessStep

private data class InitProcVarsStep(val procedure: String, val arguments: Valuation) :
  SvLibViolationWitnessStep() {

  override fun toString() = "(init-proc-vars $procedure ${arguments.toSvLib()})"
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

private fun String.indent(spaces: Int = 4) =
  this.lineSequence().joinToString("\n") { " ".repeat(spaces) + it }
