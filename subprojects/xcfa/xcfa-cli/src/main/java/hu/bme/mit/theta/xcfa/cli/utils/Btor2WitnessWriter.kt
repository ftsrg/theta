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

import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.Btor2XcfaTraceConcretizer.btor2ConcreteTrace
import hu.bme.mit.theta.xcfa.witnesses.Btor2Witness
import java.io.File

class Btor2WitnessWriter : XcfaWitnessWriter {
  override val extension: String = "sat"

  override fun writeWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    cexSolverFactory: SolverFactory,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
    logger: Logger,
  ) {
    val concrTrace =
      btor2ConcreteTrace ?: throw RuntimeException("Concrete Trace from Btor2 missing")

    val witness = Btor2Witness(badProperty = "b0")
    val regex = """T0::_::input_\w+\s+#b([01]+)""".toRegex()

    var iter = 0
    var inputIter = 0

    for (state in btor2ConcreteTrace.states) {
      val values = regex.findAll(state.sGlobal.toString()).map { it.groupValues[1] }.toList()

      if (!values.isEmpty()) {
        for (value in values) {
          witness.addInput(iter, inputIter, value)
          inputIter++
        }
        iter++
        inputIter = 0
      }
    }

    // Serialize the populated witness to the provided file
    witness.serialize(witnessfile)
    logger.write(
      Logger.Level.INFO,
      "BTOR2 witness successfully serialized to ${witnessfile.absolutePath}\n",
    )
  }

  override fun writeTrivialCorrectnessWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ) {
    TODO("Not yet implemented")
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ): String {
    TODO("Not yet implemented")
  }
}
