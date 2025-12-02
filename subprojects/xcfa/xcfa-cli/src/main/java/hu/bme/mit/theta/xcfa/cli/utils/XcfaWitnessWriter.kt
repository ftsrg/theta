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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import java.io.File

interface XcfaWitnessWriter {

  companion object {

    /**
     * Returns an appropriate witness writer for the given property, category, and safety result.
     *
     * YamlWitnessWriter corresponds to SV-COMP's witness format 2.1. GraphmlWitnessWriter
     * corresponds to SV-COMP's witness format 1.0.
     *
     * @return An instance of [XcfaWitnessWriter] suitable for the provided property and safety
     *   result, or `null` if no suitable writer is available or witnesses are not supported in that
     *   case.
     */
    fun getSvCompWitnessWriter(
      property: XcfaProperty,
      parseContext: ParseContext,
      safetyResult: SafetyResult<*, *>,
    ): XcfaWitnessWriter? =
      when (property.inputProperty) {
        ErrorDetection.ERROR_LOCATION,
        ErrorDetection.OVERFLOW ->
          if (parseContext.multiThreading) {
            safetyResult.getWitnessWriter(YamlWitnessWriter(), GraphmlWitnessWriter())
          } else {
            YamlWitnessWriter()
            // not supported witness for Arrays, Floats, and Heap is not detected
          }

        ErrorDetection.MEMSAFETY ->
          if (parseContext.multiThreading) {
            safetyResult.getWitnessWriter(null, GraphmlWitnessWriter())
          } else {
            safetyResult.getWitnessWriter(null, YamlWitnessWriter())
          }

        ErrorDetection.MEMCLEANUP -> safetyResult.getWitnessWriter(null, GraphmlWitnessWriter())

        ErrorDetection.DATA_RACE -> safetyResult.getWitnessWriter(null, GraphmlWitnessWriter())

        ErrorDetection.TERMINATION -> YamlWitnessWriter()

        else -> null
      }

    private fun SafetyResult<*, *>.getWitnessWriter(
      safeWriter: XcfaWitnessWriter?,
      unsafeWriter: XcfaWitnessWriter?,
    ): XcfaWitnessWriter? =
      when {
        isSafe -> safeWriter
        isUnsafe -> unsafeWriter
        else -> null
      }
  }

  val extension: String

  fun writeWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    cexSolverFactory: SolverFactory,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType? = null,
    logger: Logger,
  )

  fun writeTrivialCorrectnessWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType? = null,
  )

  fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ): String
}
