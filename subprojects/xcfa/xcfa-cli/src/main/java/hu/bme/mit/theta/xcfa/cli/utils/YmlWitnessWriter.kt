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

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.witnesses.*
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.toC
import java.io.File
import java.util.*
import kotlinx.serialization.encodeToString

class YmlWitnessWriter {

  fun writeWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: ErrorDetection,
    architecture: ArchitectureConfig.ArchitectureType?,
    cexSolverFactory: SolverFactory,
    parseContext: ParseContext,
    witnessfile: File,
  ) {
    val metadata =
      Metadata(
        formatVersion = "2.0",
        uuid = UUID.randomUUID().toString(),
        creationTime = getIsoDate(),
        producer =
          Producer(
            name = (System.getenv("VERIFIER_NAME") ?: "").ifEmpty { "Theta" },
            version = (System.getenv("VERIFIER_VERSION") ?: "").ifEmpty { "no version found" },
          ),
        task =
          Task(
            inputFiles = listOf(inputFile.name),
            inputFileHashes = mapOf(Pair(inputFile.path, createTaskHash(inputFile.path))),
            specification = property.name,
            dataModel =
              architecture?.let {
                if (it == ArchitectureConfig.ArchitectureType.ILP32) DataModel.ILP32
                else DataModel.LP64
              } ?: DataModel.ILP32,
            language = Language.C,
          ),
      )

    if (safetyResult.isUnsafe && safetyResult.asUnsafe().cex is Trace<*, *>) {
      val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> =
        XcfaTraceConcretizer.concretize(
          safetyResult.asUnsafe().cex as Trace<XcfaState<PtrState<*>>, XcfaAction>?,
          cexSolverFactory,
          parseContext,
        )

      val witnessTrace =
        traceToWitness(trace = concrTrace, parseContext = parseContext, property = property)

      val witness =
        YamlWitness(
          entryType = EntryType.VIOLATION,
          metadata = metadata,
          content =
            (0..(witnessTrace.length())).flatMap {
              listOfNotNull(
                witnessTrace.states
                  .get(it)
                  ?.toSegment(witnessTrace.actions.getOrNull(it - 1), inputFile),
                witnessTrace.actions.getOrNull(it)?.toSegment(inputFile),
              )
            },
        )

      witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
    } else if (safetyResult.isSafe) {

      val witness =
        YamlWitness(
          entryType = EntryType.INVARIANTS,
          metadata = metadata,
          content = safetyResult.asSafe().proof.toContent(inputFile, parseContext),
        )

      witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
    }
  }
}

private fun getLocation(inputFile: File, metadata: MetaData?): Location? {
  val line =
    (metadata as? CMetaData)?.lineNumberStart
      ?: (metadata as? CMetaData)?.lineNumberStop
      ?: return null
  val column = (metadata as? CMetaData)?.colNumberStart ?: (metadata as? CMetaData)?.colNumberStop
  return Location(fileName = inputFile.name, line = line, column = column)
}

private fun getLocation(inputFile: File, witnessEdge: WitnessEdge?): Location? {
  if (witnessEdge == null) return null
  val endLoc =
    Location(
      fileName = inputFile.name,
      line = witnessEdge.endline ?: witnessEdge.startline ?: return null,
      column = (witnessEdge.endcol ?: witnessEdge.startcol)?.plus(1),
    )
  return endLoc
}

private fun WitnessNode.toSegment(witnessEdge: WitnessEdge?, inputFile: File): ContentItem? {
  if (violation) {
    val loc = xcfaLocations.values.first().first()
    val locLoc =
      getLocation(inputFile, loc.metadata)
        ?: getLocation(inputFile, witnessEdge)
        ?: getLocation(inputFile, witnessEdge?.edge?.metadata)
        ?: return null
    return ContentItem(
      WaypointContent(type = WaypointType.TARGET, location = locLoc, action = Action.FOLLOW)
    )
  } else {
    return null
  }
}

private fun WitnessEdge.toSegment(inputFile: File): ContentItem? {
  val endLoc =
    Location(
      fileName = inputFile.name,
      line = endline ?: startline ?: return null,
      column = (endcol ?: startcol)?.plus(1),
    )
  val startLoc =
    Location(
      fileName = inputFile.name,
      line = startline ?: endline ?: return null,
      column = (startcol ?: endcol)?.plus(1),
    )

  val (loc, constraint, type) =
    if (assumption != null) {
      Triple(
        endLoc,
        Constraint(value = assumption, format = Format.C_EXPRESSION),
        WaypointType.ASSUMPTION,
      )
    } else if (control != null) {
      Triple(startLoc, Constraint(value = control.toString()), WaypointType.BRANCHING)
    } else if (enterLoopHead) {
      Triple(startLoc, Constraint(value = "true"), WaypointType.BRANCHING)
    } else if (enterFunction != null) {
      Triple(startLoc, Constraint(value = enterFunction), WaypointType.FUNCTION_ENTER)
    } else if (returnFromFunction != null) {
      Triple(endLoc, Constraint(value = returnFromFunction), WaypointType.FUNCTION_RETURN)
    } else return null
  return ContentItem(
    WaypointContent(type = type, constraint = constraint, location = loc, action = Action.FOLLOW)
  )
}

private fun Proof.toContent(inputFile: File, parseContext: ParseContext): List<ContentItem> {
  if (this is ARG<*, *>) {
    val locMap =
      nodes
        .toList()
        .mapNotNull {
          it as ArgNode<XcfaState<*>, XcfaAction>
          val loc = it.state.processes.values.firstOrNull()?.locs?.peek() ?: return@mapNotNull null
          val locLoc =
            Location(
              fileName = inputFile.name,
              line =
                (loc.metadata as? CMetaData)?.lineNumberStart
                  ?: (loc.metadata as? CMetaData)?.lineNumberStop
                  ?: return@mapNotNull null,
              column =
                (loc.metadata as? CMetaData)?.colNumberStart
                  ?: (loc.metadata as? CMetaData)?.colNumberStop,
            )
          locLoc to it.state.sGlobal.toExpr()
        }
        .groupBy { it.first }
    val invs =
      locMap
        .mapValues { entry -> ExprUtils.simplify(Or(entry.value.map { it.second })) }
        .map {
          ContentItem(
            invariant =
              Invariant(
                type = InvariantType.LOCATION_INVARIANT,
                location = it.key,
                value = it.value.toC(parseContext),
                format = Format.C_EXPRESSION,
              )
          )
        }
    return invs
  }
  return listOf()
}
