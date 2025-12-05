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
package hu.bme.mit.theta.xsts.cli

import com.github.ajalt.clikt.parameters.groups.provideDelegate
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.file
import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.MddNode
import hu.bme.mit.delta.mdd.LatticeDefinition
import hu.bme.mit.delta.mdd.MddInterpreter
import hu.bme.mit.delta.mdd.MddVariableDescriptor
import hu.bme.mit.theta.analysis.algorithm.mdd.MddAnalysisStatistics
import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import hu.bme.mit.theta.frontend.petrinet.analysis.PetriNetForceVarOrdering
import hu.bme.mit.theta.frontend.petrinet.analysis.PtNetDependency2Gxl
import hu.bme.mit.theta.frontend.petrinet.analysis.PtNetSystem
import hu.bme.mit.theta.frontend.petrinet.analysis.VariableOrderingFactory
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet
import hu.bme.mit.theta.frontend.petrinet.model.Place
import hu.bme.mit.theta.frontend.petrinet.model.PropType
import hu.bme.mit.theta.xsts.cli.optiongroup.PetrinetDependencyOutputOptions
import java.io.File
import java.io.PrintStream
import java.util.*
import javax.imageio.ImageIO
import kotlin.system.exitProcess

class XstsCliPetrinetMdd :
  XstsCliBaseCommand(
    name = "PN_MDD",
    help = "Model checking of Petri nets using MDDs (Multi-value Decision Diagrams)",
  ) {

  private val ordering: File? by
    option(help = "Path of the input variable ordering")
      .file(mustExist = true, canBeDir = false, mustBeReadable = true)
  private val id: String by
    option(help = "ID of the input model. Used for symbolic output").default("")
  private val iterationStrategy: MddChecker.IterationStrategy by
    option(help = "The state space generation algorithm to use")
      .enum<MddChecker.IterationStrategy>()
      .default(MddChecker.IterationStrategy.GSAT)
  private val dependencyOutput by PetrinetDependencyOutputOptions()

  private fun loadOrdering(petriNet: PetriNet): List<Place> =
    if (ordering == null) PetriNetForceVarOrdering.orderVars(petriNet)
    else VariableOrderingFactory.fromFile(ordering, petriNet)

  private fun petrinetAnalysis() {
    checkArgument(inputOptions.getPnProperty() == PropType.FULL_EXPLORATION) {
      "Only full exploration is supported for dedicated PN mode. Use XSTS-based analysis for other properties."
    }

    val totalTimer = Stopwatch.createStarted()
    val petriNet = inputOptions.loadPetriNet()[0]
    val effectiveOrdering = loadOrdering(petriNet)
    val system = PtNetSystem(petriNet, effectiveOrdering)
    createDepGxl(system)
    createDepGxlGSat(system)
    createDepMat(system)
    createDepMatPng(system)
    val variableOrder =
      JavaMddFactory.getDefault().createMddVariableOrder(LatticeDefinition.forSets())
    effectiveOrdering.forEach { variableOrder.createOnTop(MddVariableDescriptor.create(it)) }
    val ssgTimer = Stopwatch.createStarted()
    val provider: StateSpaceEnumerationProvider =
      when (iterationStrategy) {
        MddChecker.IterationStrategy.BFS -> BfsProvider(variableOrder)
        MddChecker.IterationStrategy.SAT -> SimpleSaturationProvider(variableOrder)
        MddChecker.IterationStrategy.GSAT -> GeneralizedSaturationProvider(variableOrder)
      }
    val stateSpace =
      provider.compute(
        system.initializer,
        system.transitions,
        variableOrder.defaultSetSignature.topVariableHandle,
      )
    ssgTimer.stop()
    totalTimer.stop()

    if (!outputOptions.benchmarkMode) {
      val statistics =
        MddAnalysisStatistics(
          0,
          MddInterpreter.calculateNonzeroCount(stateSpace),
          provider.hitCount,
          provider.queryCount,
          provider.cacheSize,
          ssgTimer.elapsedMillis(),
          totalTimer.elapsedMillis(),
        )
      logger.writeln(Logger.Level.MAINSTEP, statistics.toString())
      logger.writeln(Logger.Level.RESULT, "(SafetyResult Safe)")
    } else {
      val unionProvider = variableOrder.defaultUnionProvider
      listOf(
          id,
          inputOptions.model.path,
          system.name,
          MddInterpreter.calculateNonzeroCount(stateSpace),
          numberOfNodes(stateSpace),
          totalTimer.elapsedNanos(),
          ssgTimer.elapsedNanos(),
          variableOrder.mddGraph.uniqueTableSize,
          unionProvider.cacheSize,
          unionProvider.queryCount,
          unionProvider.hitCount,
        )
        .forEach(writer::cell)
      if (
        iterationStrategy in
          setOf(MddChecker.IterationStrategy.GSAT, MddChecker.IterationStrategy.SAT)
      ) {
        listOf(provider.cacheSize, provider.queryCount, provider.hitCount).forEach(writer::cell)
      }
      listOf(provider.cacheSize, provider.queryCount, provider.hitCount).forEach(writer::cell)
      if (
        iterationStrategy in
          setOf(MddChecker.IterationStrategy.GSAT, MddChecker.IterationStrategy.SAT)
      ) {
        val collector: MutableSet<MddNode> = mutableSetOf()
        provider.clear()
        listOf(collector.size).forEach(writer::cell)
      }
    }
  }

  private fun createDepMatPng(system: PtNetSystem) {
    if (dependencyOutput.depMatPng == null) return
    if (system.placeCount > 10000 || system.transitionCount > 10000) {
      logger.write(
        Logger.Level.INFO,
        "[WARNING] Skipping image generation because the model size exceeds 10k places or " +
          "transitions.",
      )
      return
    }
    ImageIO.write(system.dependencyMatrixImage(1), "PNG", dependencyOutput.depMatPng)
  }

  private fun createDepMat(system: PtNetSystem) {
    val file = dependencyOutput.depMat ?: return
    file.createNewFile()
    with(PrintStream(file)) { print(system.printDependencyMatrixCsv()) }
  }

  private fun createDepGxlGSat(system: PtNetSystem) {
    val file = dependencyOutput.depGxlGsat ?: return
    file.createNewFile()
    with(PrintStream(file)) { print(PtNetDependency2Gxl.toGxl(system, true)) }
  }

  private fun createDepGxl(system: PtNetSystem) {
    val file = dependencyOutput.depGxl ?: return
    file.createNewFile()
    with(PrintStream(file)) { print(PtNetDependency2Gxl.toGxl(system, false)) }
  }

  override fun run() {
    try {
      if (inputOptions.isPnml()) petrinetAnalysis()
    } catch (e: Exception) {
      printError(e)
      exitProcess(1)
    }
  }

  private fun numberOfNodes(root: MddHandle): Int {
    val result: MutableSet<MddNode> = mutableSetOf()
    val stack = Stack<MddNode>()
    stack.push(root.node)

    while (stack.isNotEmpty()) {
      val current = stack.pop()
      if (!result.add(current) || current.isTerminal) continue
      val cursor = current.cursor()
      while (cursor.moveNext()) {
        stack.push(cursor.value())
      }
    }

    return result.size
  }
}
