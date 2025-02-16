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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig

fun determineProperty(config: XcfaConfig<*, *>, logger: Logger): ErrorDetection =
  config.inputConfig.propertyFile?.run {
    val propertyFile = config.inputConfig.propertyFile!!
    when {
      propertyFile.name.endsWith("unreach-call.prp") -> {
        ErrorDetection.ERROR_LOCATION
      }

      propertyFile.name.endsWith("no-data-race.prp") -> {
        ErrorDetection.DATA_RACE
      }

      propertyFile.name.endsWith("no-overflow.prp") -> {
        ErrorDetection.OVERFLOW
      }

      propertyFile.name.endsWith("valid-memsafety.prp") -> {
        ErrorDetection.MEMSAFETY
      }

      propertyFile.name.endsWith("valid-memcleanup.prp") -> {
        ErrorDetection.MEMCLEANUP
      }

      propertyFile.name.endsWith("termination.prp") -> {
        ErrorDetection.TERMINATION
      }

      else -> {
        logger.write(
          Logger.Level.INFO,
          "Unknown property $propertyFile, using full state space exploration (no refinement)\n",
        )
        ErrorDetection.NO_ERROR
      }
    }
  } ?: config.inputConfig.property
