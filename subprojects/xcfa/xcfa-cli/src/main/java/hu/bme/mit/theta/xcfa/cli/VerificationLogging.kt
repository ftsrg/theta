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
package hu.bme.mit.theta.xcfa.cli

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.asg.HackyAsgTrace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.ltlPropertyFromTrace
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.cli.params.*
import hu.bme.mit.theta.xcfa.cli.utils.*
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.io.File

internal fun postVerificationLogging(
  xcfa: XCFA?,
  safetyResult: SafetyResult<*, *>,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  val forceEnabledOutput = config.outputConfig.enabled == OutputLevel.ALL

  val ltlSpecification =
    if (safetyResult.isUnsafe) {
      (safetyResult.asUnsafe().cex as? Trace<XcfaState<*>, XcfaAction>).let {
        config.inputConfig.property.ltlPropertyFromTrace(it)?.value
      } ?: ""
    } else {
      config.inputConfig.property.inputProperty.ltl(Unit)
    }

  if (
    config.frontendConfig.inputType == InputType.CHC &&
      xcfa != null &&
      ((config.frontendConfig.specConfig as CHCFrontendConfig).model || forceEnabledOutput)
  ) {
    writeChcAnswer(config, xcfa, safetyResult, logger)
  }

  // we only want to log the files if the current configuration is not --in-process or portfolio
  if (config.backendConfig.inProcess || config.backendConfig.backend == Backend.PORTFOLIO) {
    return
  }

  if (config.outputConfig.enabled != OutputLevel.NONE && parseContext != null) {
    try {
      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()
      logger.info("Writing post-verification artifacts to directory ${resultFolder.absolutePath}")

      // TODO eliminate the need for the instanceof check
      if (
        (forceEnabledOutput || config.outputConfig.argConfig.enabled) &&
          safetyResult.proof is ARG<out State, out Action>
      ) {
        writeArgAsProof(resultFolder, safetyResult, logger)
      }

      if (
        forceEnabledOutput ||
          config.outputConfig.argConfig.enabled && safetyResult.proof is LocationInvariants
      ) {
        writeArgAsLocInvs(resultFolder, safetyResult.proof as LocationInvariants, logger)
      }

      when {
        config.outputConfig.witnessConfig.enabled == WitnessLevel.SVCOMP -> {
          writeSvcompWitness(
            config,
            parseContext,
            safetyResult,
            resultFolder,
            ltlSpecification,
            logger,
          )
        }

        forceEnabledOutput || config.outputConfig.witnessConfig.enabled == WitnessLevel.ALL -> {
          if (safetyResult.isUnsafe && safetyResult.asUnsafe().cex != null) {
            val trace = retrieveTrace(safetyResult)
            val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
              concretizeTrace(trace, config, parseContext)

            writeTraceAsDot(resultFolder, concrTrace, logger)

            writeTraceAsPlantuml(resultFolder, trace, logger)

            writeTraceAsOptimizedPlantuml(resultFolder, concrTrace, logger)

            writeTraceAsCinPlantUml(resultFolder, concrTrace, logger)
          }

          try {
            val witnessFile = File(resultFolder, "witness.graphml")
            GraphmlWitnessWriter()
              .writeWitness(
                safetyResult,
                config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
                config.inputConfig.property,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
                witnessFile,
                ltlSpecification,
                logger = logger,
              )
          } catch (e: Exception) {
            logger.info("Could not emit witness as GraphML file: ${e.stackTraceToString()}")
          }

          try {
            val yamlWitnessFile = File(resultFolder, "witness.yml")
            YamlWitnessWriter()
              .writeWitness(
                safetyResult,
                config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
                config.inputConfig.property,
                getSolver(
                  config.outputConfig.witnessConfig.concretizerSolver,
                  config.outputConfig.witnessConfig.validateConcretizerSolver,
                ),
                parseContext,
                yamlWitnessFile,
                ltlSpecification,
                (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture,
                logger,
              )
          } catch (e: Exception) {
            logger.info("Could not emit witness as YAML file: ${e.stackTraceToString()}")
          }
        }

        else -> {}
      }
    } catch (e: Throwable) {
      logger.info("Could not output files: ${e.stackTraceToString()}")
    }
  }
}

private fun retrieveTrace(safetyResult: SafetyResult<*, *>): Cex? =
  if (safetyResult.asUnsafe().cex is HackyAsgTrace<*>) {
    val actions = (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).trace.actions
    val explStates = (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).trace.states
    val states =
      (safetyResult.asUnsafe().cex as HackyAsgTrace<*>).originalStates.mapIndexed { i, state ->
        state as XcfaState<PtrState<*>>
        state.withState(PtrState(explStates[i]))
      }

    Trace.of(states, actions)
  } else if (safetyResult.asUnsafe().cex is ASGTrace<*, *>) {
    (safetyResult.asUnsafe().cex as ASGTrace<*, *>).toTrace()
  } else {
    safetyResult.asUnsafe().cex
  }

private fun writeSequenceTrace(
  sequenceFile: File,
  trace: Trace<XcfaState<ExplState>, XcfaAction>,
  printer: (Pair<XcfaState<ExplState>, XcfaAction>) -> Sequence<String>,
) {
  sequenceFile.writeText("@startuml\n")
  var maxWidth = 0
  trace.actions.forEachIndexed { i, it ->
    val stateBefore = trace.states[i]
    sequenceFile.appendText("hnote over ${it.pid}\n")
    val labelStrings = printer(Pair(stateBefore, it))
    if (maxWidth < (labelStrings.maxOfOrNull { it.length } ?: 0)) {
      maxWidth = labelStrings.maxOfOrNull { it.length } ?: 0
    }
    sequenceFile.appendText("${labelStrings.joinToString("\n")}\n")
    sequenceFile.appendText("endhnote\n")
  }
  trace.actions
    .map { it.pid }
    .distinct()
    .reduce { acc, current ->
      sequenceFile.appendText("$acc --> $current: \"${" ".repeat(maxWidth)}\"\n")
      current
    }
  sequenceFile.appendText("@enduml\n")
}

private fun writeArgAsProof(resultFolder: File, safetyResult: SafetyResult<*, *>, logger: Logger) {
  try {
    val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
    val g: Graph =
      ArgVisualizer.getDefault().visualize(safetyResult.proof as ARG<out State, out Action>)
    argFile.writeText(GraphvizWriter.getInstance().writeString(g))
  } catch (e: Exception) {
    logger.info("Could not emit ARG as DOT file: ${e.stackTraceToString()}")
  }
}

private fun writeArgAsLocInvs(
  resultFolder: File,
  locationInvariants: LocationInvariants,
  logger: Logger,
) {
  try {
    val invFile = File(resultFolder, "invariants.txt")
    invFile.writeText("")
    for ((location, invariants) in locationInvariants.partitions) {
      invFile.appendText("${location}:\n")
      for (inv in invariants) {
        invFile.appendText("  ${inv.toString().replace(System.lineSeparator(), " ")}\n")
      }
    }
  } catch (e: Exception) {
    logger.info("Could not emit invariants file: ${e.stackTraceToString()}")
  }
}

private fun writeChcAnswer(
  config: XcfaConfig<*, *>,
  xcfa: XCFA,
  safetyResult: SafetyResult<*, *>,
  logger: Logger,
) {
  try {
    val resultFolder = config.outputConfig.resultFolder
    resultFolder.mkdirs()
    val chcAnswer = writeModel(xcfa, safetyResult)
    val chcAnswerFile = File(resultFolder, "chc-answer.smt2")
    if (chcAnswerFile.exists()) {
      logger.info("CHC answer/model already written to file $chcAnswerFile, not overwriting")
    } else {
      chcAnswerFile.writeText(chcAnswer)
      logger.info("CHC answer/model written to file $chcAnswerFile")
    }
  } catch (e: Exception) {
    logger.info("Could not write CHC answer to file: ${e.stackTraceToString()}")
  }
}

private fun writeSvcompWitness(
  config: XcfaConfig<*, *>,
  parseContext: ParseContext,
  safetyResult: SafetyResult<*, *>,
  resultFolder: File,
  ltlSpecification: String,
  logger: Logger,
) {
  try {
    val witnessWriter =
      XcfaWitnessWriter.Companion.getSvCompWitnessWriter(
        config.inputConfig.property,
        parseContext,
        safetyResult,
      )

    if (witnessWriter != null) {
      val witnessFile = File(resultFolder, "witness.${witnessWriter.extension}")
      witnessWriter.writeWitness(
        safetyResult,
        config.outputConfig.witnessConfig.inputFileForWitness ?: config.inputConfig.input!!,
        config.inputConfig.property,
        getSolver(
          config.outputConfig.witnessConfig.concretizerSolver,
          config.outputConfig.witnessConfig.validateConcretizerSolver,
        ),
        parseContext,
        witnessFile,
        ltlSpecification,
        (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture,
        logger,
      )
    } else {
      logger.info(
        "No suitable SV-COMP witness writer found for the given property (${config.inputConfig.property.inputProperty}), category (${if (parseContext.multiThreading) "concurrency" else "not concurrency"}) and safety result ($safetyResult)."
      )
    }
  } catch (e: Exception) {
    logger.info("Could not emit witness in the required SV-COMP format: ${e.stackTraceToString()}")
  }
}

private fun writeTraceAsDot(
  resultFolder: File,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
  logger: Logger,
) {
  try {
    val traceFile = File(resultFolder, "trace.dot")
    val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
    traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
  } catch (e: Exception) {
    logger.info("Could not emit trace as DOT file: ${e.stackTraceToString()}")
  }
}

private fun writeTraceAsPlantuml(resultFolder: File, trace: Cex?, logger: Logger) {
  try {
    val sequenceFile = File(resultFolder, "trace.plantuml")
    writeSequenceTrace(sequenceFile, trace as Trace<XcfaState<ExplState>, XcfaAction>) { (_, act) ->
      act.label.getFlatLabels().map(XcfaLabel::toString)
    }
  } catch (e: Exception) {
    logger.info("Could not emit trace as PlantUML file: ${e.stackTraceToString()}")
  }
}

private fun writeTraceAsOptimizedPlantuml(
  resultFolder: File,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
  logger: Logger,
) {
  try {
    val optSequenceFile = File(resultFolder, "trace-optimized.plantuml")
    writeSequenceTrace(optSequenceFile, concrTrace) { (_, act) ->
      act.label.getFlatLabels().map(XcfaLabel::toString)
    }
  } catch (e: Exception) {
    logger.info("Could not emit optimized trace as PlantUML file: ${e.stackTraceToString()}")
  }
}

private fun writeTraceAsCinPlantUml(
  resultFolder: File,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
  logger: Logger,
) {
  try {
    val cSequenceFile = File(resultFolder, "trace-c.plantuml")
    writeSequenceTrace(cSequenceFile, concrTrace) { (state, act) ->
      val proc = state.processes[act.pid]
      val loc = proc?.locs?.peek()
      (loc?.metadata as? CMetaData)?.sourceText?.split("\n")?.asSequence()
        ?: sequenceOf("<unknown>")
    }
  } catch (e: Exception) {
    logger.info("Could not emit C trace as PlantUML file: ${e.stackTraceToString()}")
  }
}
