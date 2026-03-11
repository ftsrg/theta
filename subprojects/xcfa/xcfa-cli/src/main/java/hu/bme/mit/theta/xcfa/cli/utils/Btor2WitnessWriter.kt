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
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.traceToWitness
import hu.bme.mit.theta.xcfa.witnesses.WaypointType
import java.io.File
/*
class Btor2WitnessWriter : XcfaWitnessWriter {

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
      val metadata = getMetadata(inputFile, ltlSpecification, architecture)

    if (safetyResult.isUnsafe) {
      try {
        val trace =
          safetyResult.asUnsafe().cex.let {
            if (it is HackyAsgTrace<*>) {
              val actions = (it as HackyAsgTrace<*>).trace.actions
              val explStates = (it as HackyAsgTrace<*>).trace.states
              val states =
                (it as HackyAsgTrace<*>).originalStates.mapIndexed { i, state ->
                  state as XcfaState<PtrState<*>>
                  state.withState(PtrState(explStates[i]))
                }

              Trace.of(states, actions)
            } else if (it is ASGTrace<*, *>) {
              (it as ASGTrace<*, *>).toTrace()
            } else {
              it
            }
          }
        if (trace is Trace<*, *>) {
          val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
            XcfaTraceConcretizer.concretize(
              trace as Trace<XcfaState<PtrState<*>>, XcfaAction>?,
              cexSolverFactory,
              parseContext,
            )

          var witness =
            violationWitnessFromConcreteTrace(
              concrTrace,
              metadata,
              inputFile,
              property,
              parseContext,
              witnessfile,
            )

          if (witness.content.isEmpty()) {
            logger.benchmark("Encountered empty witness, trying best-effort witness now.")
            val bestEffortWitness =
              generateBestEffortWitness(
                safetyResult,
                property,
                inputFile,
                parseContext,
                witnessfile,
                ltlSpecification,
                architecture,
              )
            witnessfile.writeText(bestEffortWitness)
          } else {
            witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
          }
        }
      } catch (e: Exception) {
        logger.benchmark(
          "Could not emit witness, writing reachability witness with target only if possible"
        )
        val bestEffortWitness =
          generateBestEffortWitness(
            safetyResult,
            property,
            inputFile,
            parseContext,
            witnessfile,
            ltlSpecification,
            architecture,
          )
        witnessfile.writeText(bestEffortWitness)
      }
    } else if (safetyResult.isSafe) {
      try {
        val witness =
          YamlWitness(
            entryType = EntryType.INVARIANTS,
            metadata = metadata,
            content = safetyResult.asSafe().proof.toContent(inputFile, parseContext),
          )

        witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
      } catch (e: Exception) {
        logger.info("Could not emit witness, outputting empty witness")
      }
    }
  }

  val witnessTrace =
    traceToWitness(trace = concrTrace, parseContext = parseContext, property = property)

  val content =
    (0..(witnessTrace.length()))
      .flatMap {
        listOfNotNull(
          witnessTrace.states[it]?.toSegment(
            witnessTrace.actions.getOrNull(it - 1),
            witnessTrace.actions.getOrNull(it),
            inputFile,
            parseContext = parseContext,
            violation =
            witnessTrace.states[it].violation ||
              witnessTrace.states.getOrNull(it + 1)?.violation ?: false,
          ),
          witnessTrace.actions.getOrNull(it)?.toSegment(inputFile),
        )
      }
      .let { it.subList(0, it.indexOfFirst { it.type == WaypointType.TARGET } + 1) }
      .let { list ->
        list.filter {
          !functionReturnOnly ||
            it.type == WaypointType.TARGET ||
            it.type == WaypointType.FUNCTION_RETURN
        }
      }
      .map { ContentItem(it) }

  return YamlWitness(entryType = EntryType.VIOLATION, metadata = metadata, content = content)

}
*/