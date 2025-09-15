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
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.*
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.witnesses.*
import java.io.File
import java.util.*
import kotlinx.serialization.encodeToString

class YamlWitnessWriter {

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

      val witness =
        if (property == ErrorDetection.TERMINATION) {
          // last state is cycle_head, find its earliest occurrence
          // stem is everything beforehand
          // cycle's segments are everything in-between

          val cycleHead = concrTrace.states.last()
          val cycleHeadFirst =
            concrTrace.states.indexOfFirst {
              it.processes.values.map { it.locs } == cycleHead.processes.values.map { it.locs } &&
                it.sGlobal == cycleHead.sGlobal
            }
          if (cycleHeadFirst == -1) {
            error("Lasso not found")
          }
          val stem =
            Trace.of(
              concrTrace.states.subList(0, cycleHeadFirst - 1),
              concrTrace.actions.subList(0, cycleHeadFirst - 2),
            )
          val lasso = // TODO this works for CHCs, with the CHC backend, but adds wrong location in
            // case of e.g., BMC !!
            Trace.of(
              concrTrace.states.subList(cycleHeadFirst, concrTrace.states.size - 1),
              concrTrace.actions.subList(cycleHeadFirst, concrTrace.actions.size - 1),
            )

          val backEdge =
            Trace.of(
              concrTrace.states.subList(concrTrace.states.size - 2, concrTrace.states.size),
              concrTrace.actions.subList(concrTrace.actions.size - 1, concrTrace.actions.size),
            )

          val stemTrace =
            traceToWitness(trace = stem, parseContext = parseContext, property = property)
          val lassoTrace =
            traceToWitness(trace = lasso, parseContext = parseContext, property = property)
          val backEdgeTrace =
            traceToWitness(trace = backEdge, parseContext = parseContext, property = property)

          YamlWitness(
            entryType = EntryType.VIOLATION,
            metadata = metadata,
            content =
              (0..(stemTrace.length()))
                .flatMap {
                  listOfNotNull(
                    stemTrace.states
                      .get(it)
                      ?.toSegment(stemTrace.actions.getOrNull(it - 1), inputFile),
                    stemTrace.actions.getOrNull(it)?.toSegment(inputFile),
                  )
                }
                .map { ContentItem(it) } +
                ContentItem(
                  WaypointContent(
                    type = WaypointType.RECURRENCE_CONDITION,
                    location =
                      ((lasso.actions.first().edge.metadata as? CMetaData)?.astNodes?.first()
                          ?: error("Cycle's metadata is missing."))
                        .let {
                          Location(
                            fileName = inputFile.name,
                            line = it.lineNumberStart,
                            column = it.colNumberStart + 1,
                          )
                        },
                    constraint =
                      Constraint(
                        value =
                          cycleHead.sGlobal.toExpr().replaceVars(parseContext).toC(parseContext),
                        format = Format.C_EXPRESSION,
                      ),
                    action = Action.CYCLE,
                  )
                ) +
                (0..<lassoTrace.length())
                  .flatMap {
                    listOfNotNull(
                      lassoTrace.states
                        .get(it)
                        ?.toSegment(lassoTrace.actions.getOrNull(it - 1), inputFile, Action.CYCLE),
                      lassoTrace.actions.getOrNull(it)?.toSegment(inputFile, Action.CYCLE),
                    )
                  }
                  .map { ContentItem(it) },
          )
        } else {
          val witnessTrace =
            traceToWitness(trace = concrTrace, parseContext = parseContext, property = property)

          YamlWitness(
            entryType = EntryType.VIOLATION,
            metadata = metadata,
            content =
              (0..(witnessTrace.length()))
                .flatMap {
                  listOfNotNull(
                    witnessTrace.states
                      .get(it)
                      ?.toSegment(witnessTrace.actions.getOrNull(it - 1), inputFile),
                    witnessTrace.actions.getOrNull(it)?.toSegment(inputFile),
                  )
                }
                .map { ContentItem(it) },
          )
        }

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

private fun Expr<BoolType>.replaceVars(parseContext: ParseContext): Expr<BoolType> {
  val vars =
    ExprUtils.getVars(this).associateWith {
      val cname = parseContext.metadata.getMetadataValue(it.name, "cName")
      if (cname.isPresent) Var(cname.get() as String, it.type) else it
    }
  return this.changeVars(vars)
}

private fun getLocation(inputFile: File, metadata: MetaData?): Location? {
  val line =
    (metadata as? CMetaData)?.lineNumberStart
      ?: (metadata as? CMetaData)?.lineNumberStop
      ?: return null
  val column = (metadata as? CMetaData)?.colNumberStart ?: (metadata as? CMetaData)?.colNumberStop
  return Location(fileName = inputFile.name, line = line, column = column?.plus(1))
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

private fun WitnessNode.toSegment(
  witnessEdge: WitnessEdge?,
  inputFile: File,
  action: Action = Action.FOLLOW,
): WaypointContent? {
  if (violation) {
    val loc = xcfaLocations.values.first().first()
    val locLoc =
      getLocation(inputFile, loc.metadata)
        ?: getLocation(inputFile, witnessEdge)
        ?: getLocation(inputFile, witnessEdge?.edge?.metadata)
        ?: return null
    return WaypointContent(type = WaypointType.TARGET, location = locLoc, action = action)
  } else {
    return null
  }
}

private fun WitnessEdge.toSegment(
  inputFile: File,
  action: Action = Action.FOLLOW,
): WaypointContent? {
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
        Constraint(value = assumption!!, format = Format.C_EXPRESSION),
        WaypointType.ASSUMPTION,
      )
    } else if (control != null) {
      Triple(startLoc, Constraint(value = control.toString()), WaypointType.BRANCHING)
    } else if (enterLoopHead) {
      Triple(startLoc, Constraint(value = "true"), WaypointType.BRANCHING)
    } else if (enterFunction != null) {
      Triple(startLoc, Constraint(value = enterFunction!!), WaypointType.FUNCTION_ENTER)
    } else if (returnFromFunction != null) {
      Triple(endLoc, Constraint(value = returnFromFunction!!), WaypointType.FUNCTION_RETURN)
    } else return null
  return WaypointContent(type = type, constraint = constraint, location = loc, action = action)
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
