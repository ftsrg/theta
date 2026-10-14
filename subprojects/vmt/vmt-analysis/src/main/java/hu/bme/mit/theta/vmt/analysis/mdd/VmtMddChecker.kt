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
package hu.bme.mit.theta.vmt.analysis.mdd

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddSignature
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodeNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.MddNodePostcondition
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OnTheFlyReachabilityNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.OrNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl.ReverseNextStateDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.IterationStrategy
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.SingleStepProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.TraceProvider
import hu.bme.mit.theta.analysis.algorithm.mdd.result.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.vmt.VmtModel
import hu.bme.mit.theta.vmt.VmtProperty
import hu.bme.mit.theta.vmt.VmtStateVar

/**
 * Saturation-based reachability over a [VmtModel], with every formula kept as a JavaSMT term of the
 * model's formula manager. The JavaSMT counterpart of the expression-based MDD checker.
 *
 * Each top-level disjunct of the transition relation becomes one next-state descriptor. Input
 * variables are not MDD levels: the solver quantifies them existentially when it checks an edge.
 * [proverPool] must use the solver context that created the model's formulas.
 */
class VmtMddChecker
@JvmOverloads
constructor(
  private val model: VmtModel,
  private val proverPool: FormulaProverPool,
  private val logger: Logger,
  private val property: VmtProperty? = model.invariantProperties.firstOrNull(),
  private val iterationStrategy: IterationStrategy = IterationStrategy.GSAT,
  private val variableOrdering: List<VmtStateVar> = model.stateVars,
  private val lookAhead: FormulaMddRepresentation.LookAhead =
    FormulaMddRepresentation.LookAhead.VARIABLE_LEVEL,
  private val edgeLimit: Int = FormulaMddContext.DEFAULT_EDGE_LIMIT,
) : SafetyChecker<VmtMddProof, VmtTrace, UnitPrec> {

  override fun check(prec: UnitPrec?): SafetyResult<VmtMddProof, VmtTrace> {
    val totalTime = Stopwatch.createStarted()

    Preconditions.checkArgument(
      property == null || property.kind == VmtProperty.Kind.INVARIANT,
      "Only invariant properties are supported, got %s",
      property?.kind,
    )
    Preconditions.checkArgument(
      variableOrdering.size == model.stateVars.size &&
        variableOrdering.toSet() == model.stateVars.toSet(),
      "Variable ordering must contain every state variable exactly once",
    )
    for (v in variableOrdering) {
      Preconditions.checkArgument(
        FormulaMddContext.isSupported(v.type),
        "Unsupported type %s of state variable %s",
        v.type,
        v.name,
      )
    }

    val levelVars =
      variableOrdering.map {
        FormulaVar(it.name, it.current, it.type, false) to
          FormulaVar(it.nextName, it.next, it.type, true)
      }
    val ctx =
      FormulaMddContext(
        model.formulaManager,
        proverPool,
        levelVars.flatMap { it.toList() },
        edgeLimit,
      )
    val bmgr = ctx.booleanFormulaManager

    val mddGraph = JavaMddFactory.getDefault().createMddGraph(ctx.latticeDefinition())
    val mddGraph2 = JavaMddFactory.getDefault().createMddGraph(ctx.latticeDefinition())
    mddGraph.setAttribute(FormulaMddRepresentation.LOOK_AHEAD, lookAhead)
    mddGraph2.setAttribute(FormulaMddRepresentation.LOOK_AHEAD, lookAhead)

    val stateOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph)
    val transOrder = JavaMddFactory.getDefault().createMddVariableOrder(mddGraph2)

    for ((current, next) in levelVars.reversed()) {
      stateOrder.createOnTop(MddVariableDescriptor.create(current, 0))
      transOrder.createOnTop(MddVariableDescriptor.create(next, 0))
      transOrder.createOnTop(MddVariableDescriptor.create(current, 0))
    }

    val stateSig = stateOrder.defaultSetSignature
    val transSig = transOrder.defaultSetSignature

    val checksBefore = proverPool.checkCount
    val ssgTime = Stopwatch.createStarted()

    val initNode = stateSig.topVariableHandle.checkInNode(FormulaMddTemplate.of(model.init, ctx))
    logger.write(Logger.Level.INFO, "Created initial node\n")

    val transNodes = mutableListOf<MddHandle>()
    val descriptors = mutableListOf<AbstractNextStateDescriptor>()
    for (formula in model.transSplit) {
      val transitionNode =
        transSig.topVariableHandle.checkInNode(FormulaMddTemplate.of(formula, ctx, true))
      transNodes.add(transitionNode)
      descriptors.add(MddNodeNextStateDescriptor.of(transitionNode))
    }
    val nextStates: AbstractNextStateDescriptor = OrNextStateDescriptor.create(descriptors)

    val propFormula = property?.formula ?: bmgr.makeTrue()
    val propNode =
      stateSig.topVariableHandle.checkInNode(FormulaMddTemplate.of(bmgr.not(propFormula), ctx))
    val targetedNextStates =
      if (bmgr.isTrue(propFormula)) nextStates
      else OnTheFlyReachabilityNextStateDescriptor.of(nextStates, propNode)

    logger.write(Logger.Level.INFO, "Created next-state node, starting fixed point calculation\n")
    val stateSpaceProvider = iterationStrategy.createProvider(stateSig.variableOrder)
    val stateSpace =
      stateSpaceProvider.compute(
        MddNodePostcondition.of(initNode),
        targetedNextStates,
        stateSig.topVariableHandle,
      )
    ssgTime.stop()

    logger.write(
      Logger.Level.INFO,
      "Solver check() calls: ${proverPool.checkCount - checksBefore}\n",
    )

    val propViolating = stateSpace.intersection(propNode)
    val violatingSize = MddInterpreter.calculateNonzeroCount(propViolating)
    logger.write(Logger.Level.INFO, "States violating the property: $violatingSize\n")
    val stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace)
    logger.write(Logger.Level.DETAIL, "State space size: $stateSpaceSize\n")

    totalTime.stop()
    val statistics =
      MddAnalysisStatistics(
        violatingSize,
        stateSpaceSize,
        stateSpaceProvider.hitCount,
        stateSpaceProvider.queryCount,
        stateSpaceProvider.cacheSize,
        ssgTime.elapsedMillis(),
        totalTime.elapsedMillis(),
      )
    logger.write(Logger.Level.MAINSTEP, "%s\n", statistics)

    val proof = VmtMddProof(stateSpace)
    return if (violatingSize != 0L) {
      val trace = generateTrace(ctx, transNodes, stateSpace, propViolating, initNode, stateSig)
      SafetyResult.unsafe(trace, proof, statistics)
    } else {
      SafetyResult.safe(proof, statistics)
    }
  }

  // Runs on the calling thread: the solver context must not be used by two threads at once.
  private fun generateTrace(
    ctx: FormulaMddContext,
    transNodes: List<MddHandle>,
    stateSpace: MddHandle,
    propViolating: MddHandle,
    initNode: MddHandle,
    stateSig: MddSignature,
  ): VmtTrace {
    logger.mainStep("Starting trace generation.\n")
    val traceTime = Stopwatch.createStarted()

    // an initially violating state must be the seed, or the search may end in a non-initial one
    val initViolating = propViolating.intersection(initNode)
    val traceSeed =
      if (MddInterpreter.calculateNonzeroCount(initViolating) > 0) initViolating else propViolating

    val forward = transNodes.map { MddNodeNextStateDescriptor.of(it) }
    val reversed =
      OrNextStateDescriptor.create(transNodes.map { ReverseNextStateDescriptor.of(stateSpace, it) })
    val top = stateSig.topVariableHandle
    val traceProvider = TraceProvider(stateSig.variableOrder)
    val stepper = SingleStepProvider(stateSig.variableOrder)
    val states = ArrayList<MddHandle>()
    val transitions = ArrayList<Int>()
    try {
      val layers = traceProvider.compute(traceSeed, reversed, initNode, top)
      states.add(layers[0].satOne())
      for (k in 0 until layers.size - 1) {
        val fired =
          forward.withIndex().firstNotNullOfOrNull { (index, transition) ->
            val successors =
              stepper
                .compute(MddNodePostcondition.of(states[k]), transition, top)
                .intersection(layers[k + 1])
            if (successors.isTerminalZero) null else index to successors.satOne()
          }
        if (fired != null) {
          transitions.add(fired.first)
          states.add(fired.second)
        } else {
          transitions.add(-1)
          states.add(layers[k + 1].satOne())
        }
      }
    } finally {
      traceProvider.dispose()
      stepper.clear()
      stepper.dispose()
    }

    traceTime.stop()
    logger.mainStep("Trace generation finished in ${traceTime.elapsedMillis()}ms.\n")
    return VmtTrace(states.map { valuationOf(it, ctx) }, transitions)
  }

  /** The values along the first path of [state]; a level skipped by a default edge is omitted. */
  private fun valuationOf(state: MddHandle, ctx: FormulaMddContext): Map<String, Any> {
    val values = LinkedHashMap<String, Any>()
    var node = state
    while (!node.isTerminal) {
      if (!node.defaultValue().isTerminalZero) {
        node = node.defaultValue()
      } else {
        val cursor = node.cursor()
        check(cursor.moveNext()) { "Empty node on a counterexample path" }
        val variable = node.variableHandle.variable.orElseThrow()
        val formulaVar = variable.traceInfo as FormulaVar
        values[formulaVar.name] = ctx.toValue(cursor.key(), formulaVar)
        node = cursor.value() as MddHandle
      }
    }
    return values
  }
}
