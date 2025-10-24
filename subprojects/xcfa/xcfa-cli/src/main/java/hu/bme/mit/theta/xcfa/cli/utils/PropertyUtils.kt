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

import com.beust.jcommander.IStringConverter
import com.beust.jcommander.ParameterException
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.ErrorDetection.*
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.params.XcfaConfig

fun determineProperty(config: XcfaConfig<*, *>, logger: Logger): XcfaProperty =
  config.inputConfig.propertyFile
    ?.run {
      val propertyFile = config.inputConfig.propertyFile!!
      when {
        propertyFile.name.endsWith("unreach-call.prp") -> ERROR_LOCATION
        propertyFile.name.endsWith("no-data-race.prp") -> DATA_RACE
        propertyFile.name.endsWith("no-overflow.prp") -> OVERFLOW
        propertyFile.name.endsWith("valid-memsafety.prp") -> MEMSAFETY
        propertyFile.name.endsWith("valid-memcleanup.prp") -> MEMCLEANUP
        propertyFile.name.endsWith("termination.prp") -> TERMINATION

        else -> {
          logger.write(
            Logger.Level.INFO,
            "Unknown property $propertyFile, using full state space exploration (no refinement)\n",
          )
          NO_ERROR
        }
      }
    }
    ?.let { XcfaProperty(it) } ?: config.inputConfig.property

class StringToXcfaPropertyConverter : IStringConverter<XcfaProperty> {
  override fun convert(input: String): XcfaProperty {
    val errorDetection =
      try {
        valueOf(input.uppercase())
      } catch (_: IllegalArgumentException) {
        val allowed = ErrorDetection.entries.joinToString(", ") { it.name }
        throw ParameterException("Invalid value '$input'. Allowed values: [$allowed]")
      }
    return XcfaProperty(errorDetection)
  }
}
