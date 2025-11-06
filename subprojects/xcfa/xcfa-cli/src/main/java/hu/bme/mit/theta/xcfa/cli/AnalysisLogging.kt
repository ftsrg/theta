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

import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.graphsolver.patterns.constraints.MCM
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.params.HornConfig
import hu.bme.mit.theta.xcfa.cli.params.OutputLevel
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig
import hu.bme.mit.theta.xcfa.cli.utils.getGson
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa2chc.RankingFunction
import hu.bme.mit.theta.xcfa2chc.toSMT2CHC
import java.io.File

internal fun preAnalysisLogging(
  xcfa: XCFA,
  mcm: MCM,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
  uniqueLogger: Logger,
) {
  if (config.outputConfig.enabled != OutputLevel.NONE) {
    try {
      val enabled = config.outputConfig.enabled == OutputLevel.ALL
      val resultFolder = config.outputConfig.resultFolder
      resultFolder.mkdirs()

      logger.info(
        "Writing pre-verification artifacts to directory ${resultFolder.absolutePath} with config ${config.outputConfig}"
      )

      if (enabled || config.outputConfig.chcOutputConfig.enabled) {
        writeChc(xcfa, resultFolder, config, logger)
      }

      if (enabled || config.outputConfig.xcfaOutputConfig.enabled) {
        writeXcfaAsDot(resultFolder, xcfa, logger)

        writeXcfaAsJson(resultFolder, xcfa, logger)
      }

      if (enabled || config.outputConfig.cOutputConfig.enabled) {
        writeXcfaAsC(resultFolder, xcfa, parseContext, config, logger)
      }
    } catch (e: Throwable) {
      logger.info("Could not output files: ${e.stackTraceToString()}")
    }
  }
}

private fun writeXcfaAsC(
  resultFolder: File,
  xcfa: XCFA,
  parseContext: ParseContext,
  config: XcfaConfig<*, *>,
  logger: Logger,
) {
  try {
    val xcfaCFile = File(resultFolder, "xcfa.c")
    xcfaCFile.writeText(
      xcfa.toC(
        parseContext,
        config.outputConfig.cOutputConfig.useArr,
        config.outputConfig.cOutputConfig.useExArr,
        config.outputConfig.cOutputConfig.useRange,
      )
    )
  } catch (e: Throwable) {
    logger.info("Could not emit XCFA as C file: ${e.stackTraceToString()}")
  }
}

private fun writeXcfaAsJson(resultFolder: File, xcfa: XCFA, logger: Logger) {
  try {
    val xcfaJsonFile = File(resultFolder, "xcfa.json")
    val uglyJson = getGson(xcfa).toJson(xcfa)
    val create = GsonBuilder().setPrettyPrinting().create()
    xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
  } catch (e: Exception) {
    logger.info("Could not emit XCFA as JSON file: ${e.stackTraceToString()}")
  }
}

private fun writeXcfaAsDot(resultFolder: File, xcfa: XCFA, logger: Logger) {
  try {
    val xcfaDotFile = File(resultFolder, "xcfa.dot")
    xcfaDotFile.writeText(xcfa.toDot())
  } catch (e: Exception) {
    logger.info("Could not emit XCFA as DOT file: ${e.stackTraceToString()}")
  }
}

private fun writeChc(xcfa: XCFA, resultFolder: File, config: XcfaConfig<*, *>, logger: Logger) {
  xcfa.procedures.forEach {
    try {
      val chcFile = File(resultFolder, "xcfa-${it.name}.smt2")
      chcFile.writeText(
        it.toSMT2CHC(
          config.inputConfig.property.verifiedProperty == ErrorDetection.TERMINATION,
          (config.backendConfig.specConfig as? HornConfig)?.rankingFuncConstr ?: RankingFunction.ADD,
        )
      )
    } catch (e: Exception) {
      logger.info("Could not emit XCFA as CHC file: ${e.stackTraceToString()}")
    }
  }
}
