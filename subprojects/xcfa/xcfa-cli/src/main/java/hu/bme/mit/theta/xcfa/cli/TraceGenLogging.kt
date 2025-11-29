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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSet
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.params.CFrontendConfig
import hu.bme.mit.theta.xcfa.cli.params.OutputLevel
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.YamlWitnessWriter
import hu.bme.mit.theta.xcfa.witnesses.WitnessYamlConfig
import java.io.File
import java.io.PrintWriter
import kotlinx.serialization.encodeToString

internal fun postTraceGenerationLogging(
  result:
    TraceGenerationResult<AbstractTraceSet<XcfaState<*>, XcfaAction>, XcfaState<*>, XcfaAction>,
  mcm: MCM?,
  parseContext: ParseContext?,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  config.outputConfig.enabled = OutputLevel.ALL
  val forceEnabledOutput = config.outputConfig.enabled == OutputLevel.ALL

  /*
  val abstractSummary = result.summary
  logger.write(
    Logger.Level.MAINSTEP,
    "Successfully generated a summary of ${abstractSummary.sourceTraces.size} abstract traces.\n",
  )
   */

  val resultFolder = config.outputConfig.resultFolder
  resultFolder.mkdirs()

  if (forceEnabledOutput && parseContext != null) {
    logger.write(
      Logger.Level.MAINSTEP,
      "Writing post-verification artifacts to directory ${resultFolder.absolutePath}\n",
    )
    val modelName = config.inputConfig.input!!.name
    /*
        val graph = AbstractTraceSummaryVisualizer.visualize(abstractSummary)
        val visFile =
          resultFolder.absolutePath + File.separator + modelName + ".abstract-trace-summary.png"
        GraphvizWriter.getInstance().writeFileAutoConvert(graph, visFile)
        logger.write(Logger.Level.SUBSTEP, "Abstract trace summary was visualized in ${visFile}\n")
    */
    var concreteTraces = 1
    for (abstractTrace in result.summary.sourceTraces) {
      try {
        // TODO no concrete summary implemented for XCFA yet, only traces
        // TODO also, if I add a --witness for tracegen, I don't get back the function returns in
        // the output witness, they are not the same (why? outdated concretization? idk)
        val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
          concretizeTrace(abstractTrace.toTrace(), config, parseContext)

        val concreteTraceFile =
          writeTraceAsFile(resultFolder, modelName, concreteTraces, concrTrace)

        val concreteDotFile = writeTraceAsDot(resultFolder, modelName, concreteTraces, concrTrace)

        val yamlWitnessFile =
          writeTraceAsYaml(
            logger,
            resultFolder,
            concreteTraces,
            config,
            config.inputConfig.input,
            concrTrace,
            parseContext,
          )

        if (yamlWitnessFile != null) {
          logger.write(
            Logger.Level.RESULT,
            "Concrete trace exported to ${concreteTraceFile}, ${yamlWitnessFile} and ${concreteDotFile}\n",
          )
        } else {
          logger.write(
            Logger.Level.RESULT,
            "Concrete trace exported to ${concreteTraceFile}, and ${concreteDotFile}\n Witness export failed\n",
          )
        }
        concreteTraces++
      } catch (e: IllegalArgumentException) {
        logger.write(Logger.Level.SUBSTEP, e.toString())
        logger.write(Logger.Level.SUBSTEP, "\nContinuing concretization with next trace...\n")
      }
    }
    logger.write(
      Logger.Level.RESULT,
      "\nSuccessfully generated ${concreteTraces-1} concrete traces.\n",
    )
  }

  // TODO print coverage (full or not)?
}

private fun writeTraceAsYaml(
  logger: Logger,
  resultFolder: File,
  concreteTraces: Int,
  config: XcfaConfig<*, *>,
  input: File?,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
  parseContext: ParseContext,
): File? {
  val yamlWitnessFile = File(resultFolder, "witness-$concreteTraces.yml")
  val inputfile = config.outputConfig.witnessConfig.inputFileForWitness ?: input!!
  val property = ErrorDetection.ERROR_LOCATION
  val ltlSpecification = ErrorDetection.ERROR_LOCATION.ltl(Unit)
  val architecture = (config.frontendConfig.specConfig as? CFrontendConfig)?.architecture
  val witnessWriter = YamlWitnessWriter()
  val witness =
    witnessWriter.generateTracegenWitnessFromConcreteTrace(
      concrTrace,
      witnessWriter.getMetadata(inputfile, ltlSpecification, architecture),
      inputfile,
      property,
      ltlSpecification,
      parseContext!!,
      yamlWitnessFile,
    )

  if (witness.content.isNotEmpty()) {
    yamlWitnessFile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
    return yamlWitnessFile
  } else {
    return null
  }
}

private fun writeTraceAsDot(
  resultFolder: File,
  modelName: String,
  concreteTraces: Int,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
): File {
  val concreteDotFile =
    File(resultFolder.absolutePath + File.separator + modelName + "_${concreteTraces}.dot")
  val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
  concreteDotFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
  return concreteDotFile
}

private fun writeTraceAsFile(
  resultFolder: File,
  modelName: String,
  concreteTraces: Int,
  concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
): String {
  val concreteTraceFile =
    resultFolder.absolutePath + File.separator + modelName + "_${concreteTraces}.cex"

  PrintWriter(File(concreteTraceFile)).use { printWriter ->
    printWriter.write(concrTrace.toString())
  }
  return concreteTraceFile
}
