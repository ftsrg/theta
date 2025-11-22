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
import hu.bme.mit.theta.analysis.algorithm.EmptyProof
import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.asg.HackyAsgTrace
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.getCMetaData
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.fptype.FpLitExpr
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.model.statements.CCall
import hu.bme.mit.theta.frontend.transformation.model.statements.CIf
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.solver.SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.witnesstransformation.*
import hu.bme.mit.theta.xcfa.model.ChoiceType
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.*
import java.io.File
import java.util.*
import kotlinx.serialization.encodeToString

class YamlWitnessWriter : XcfaWitnessWriter {

  override val extension: String = "yml"

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
            logger.result("Encountered empty witness, trying best-effort witness now.")
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
        logger.result(
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

  private fun generateBestEffortWitness(
    safetyResult: SafetyResult<*, *>,
    property: XcfaProperty,
    inputFile: File,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ): String {

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
          it as Trace<*, XcfaAction>
        }
      }

    val lastLabel =
      (trace as Trace<*, XcfaAction>)
        .actions
        .flatMap { it.label.getFlatLabels() }
        .findLast { it -> it.metadata.isSubstantial() }
    if (lastLabel == null)
      return generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
    val metadata = lastLabel.getCMetaData()

    return if (property.inputProperty == ErrorDetection.ERROR_LOCATION) {
      val call = metadata?.astNodes?.find { it -> it is CCall && it.functionId == "reach_error" }
      call?.let {
        val loc = Location(inputFile.name, it.lineNumberStart, it.colNumberStart + 1)
        generateTrivialViolationWitness(
          safetyResult = safetyResult,
          inputFile = inputFile,
          property = property,
          parseContext = parseContext,
          witnessfile = witnessfile,
          ltlSpecification = ltlSpecification,
          architecture = architecture,
          targetLocation = loc,
        )
      } ?: generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
    } else if (
      listOf(ErrorDetection.OVERFLOW, ErrorDetection.MEMCLEANUP, ErrorDetection.MEMSAFETY)
        .contains(property.inputProperty)
    ) {
      getLocation(inputFile, metadata)?.let {
        generateTrivialViolationWitness(
          safetyResult = safetyResult,
          inputFile = inputFile,
          property = property,
          parseContext = parseContext,
          witnessfile = witnessfile,
          ltlSpecification = ltlSpecification,
          architecture = architecture,
          targetLocation = it,
        )
      } ?: generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
    } else generateEmptyViolationWitness(inputFile, ltlSpecification, architecture)
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
    val metadata = getMetadata(inputFile, ltlSpecification, architecture)
    val witness =
      YamlWitness(
        entryType = EntryType.INVARIANTS,
        metadata = metadata,
        content = EmptyProof.getInstance().toContent(inputFile, parseContext),
      )
    witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
  }

  override fun generateEmptyViolationWitness(
    inputFile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
  ): String {
    val metadata = getMetadata(inputFile, ltlSpecification, architecture)
    return WitnessYamlConfig.encodeToString(
      listOf(YamlWitness(entryType = EntryType.VIOLATION, metadata = metadata, content = listOf()))
    )
  }

  fun generateTrivialViolationWitness(
    safetyResult: SafetyResult<*, *>,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    ltlSpecification: String,
    architecture: ArchitectureConfig.ArchitectureType?,
    targetLocation: Location,
  ): String {
    val metadata = getMetadata(inputFile, ltlSpecification, architecture)
    val witness =
      YamlWitness(
        entryType = EntryType.VIOLATION,
        metadata = metadata,
        content =
          listOf(
            ContentItem(
              listOf(
                Waypoint(
                  WaypointContent(
                    WaypointType.TARGET,
                    null,
                    location = targetLocation,
                    Action.FOLLOW,
                  )
                )
              )
            )
          ),
      )
    return WitnessYamlConfig.encodeToString(listOf(witness))
  }

  fun getMetadata(
    inputFile: File,
    ltlSpecification:
      String, // ErrorDetection enum is not enough, several violation specifications can fit for a
    // single ErrorDetection value
    architecture: ArchitectureConfig.ArchitectureType?,
  ): Metadata {
    return Metadata(
      formatVersion = "2.1",
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
          specification = ltlSpecification,
          dataModel =
            architecture?.let {
              if (it == ArchitectureConfig.ArchitectureType.ILP32) DataModel.ILP32
              else DataModel.LP64
            } ?: DataModel.ILP32,
          language = Language.C,
        ),
    )
  }

  fun tracegenWitnessFromConcreteTrace(
    concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
    metadata: Metadata,
    inputFile: File,
    property: ErrorDetection,
    ltlViolationProperty: String,
    parseContext: ParseContext,
    witnessfile: File,
  ) {
    check(property == ErrorDetection.ERROR_LOCATION)
    val witnessTrace =
      traceToWitness(
        trace = concrTrace,
        parseContext = parseContext,
        property = XcfaProperty(property),
      )

    val waypoints =
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
        .let {
          if (it.any { wp -> wp.type == WaypointType.TARGET })
            it.subList(0, it.indexOfFirst { it.type == WaypointType.TARGET } + 1)
          else it
        }
        .toMutableList()

    if (!waypoints.any { wp -> wp.type == WaypointType.TARGET }) {
      val last = waypoints.last()
      val newLast =
        last.copy(type = WaypointType.TARGET, constraint = null) // change last follow to be target
      waypoints[waypoints.size - 1] = newLast
    }
    val witnessContent = waypoints.map { ContentItem(it) }

    val witness =
      YamlWitness(entryType = EntryType.VIOLATION, metadata = metadata, content = witnessContent)

    witnessfile.writeText(WitnessYamlConfig.encodeToString(listOf(witness)))
  }

  private fun terminationViolationWitnessFromConcreteTrace(
    concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
    metadata: Metadata,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
  ): YamlWitness {
    // last state is cycle_head, find its earliest occurrence
    // stem is everything beforehand
    // cycle's segments are everything in-between

    val cycleHead = concrTrace.states.last()
    val cycleHeadFirst =
      concrTrace.states
        .indexOfFirst {
          it.processes.values.map { it.locs } == cycleHead.processes.values.map { it.locs } &&
            it.sGlobal == cycleHead.sGlobal
        }
        .let { index ->
          if (index == concrTrace.states.size - 1) {
            // we go backwards, and find a candidate.
            val revIdx =
              1 +
                concrTrace.states.subList(0, concrTrace.states.size - 1).reversed().indexOfFirst {
                  it.processes.values.map { it.locs } ==
                    cycleHead.processes.values.map { it.locs } &&
                    it.sGlobal.toMap().all { (key, value) ->
                      cycleHead.sGlobal.toMap()[key] == value
                    }
                }
            concrTrace.states.size - 1 - revIdx
          } else {
            index
          }
        }
    if (cycleHeadFirst == -1) {
      error("Lasso not found")
    }
    val stem =
      Trace.of(
        concrTrace.states.subList(0, cycleHeadFirst + 1),
        concrTrace.actions.subList(0, cycleHeadFirst),
      )
    val lasso = // TODO this works for CHCs, with the CHC backend, but adds wrong location in
      // case of e.g., BMC !!
      Trace.of(
        concrTrace.states.subList(cycleHeadFirst, concrTrace.states.size),
        concrTrace.actions.subList(cycleHeadFirst, concrTrace.actions.size),
      )

    val stemTrace = traceToWitness(trace = stem, parseContext = parseContext, property = property)
    val lassoTrace = traceToWitness(trace = lasso, parseContext = parseContext, property = property)

    return YamlWitness(
      entryType = EntryType.VIOLATION,
      metadata = metadata,
      content =
        (0..(stemTrace.length() - 1))
          .flatMap {
            listOfNotNull(
              stemTrace.states
                .get(it)
                ?.toSegment(
                  stemTrace.actions.getOrNull(it - 1),
                  stemTrace.actions.getOrNull(it),
                  inputFile,
                  parseContext = parseContext,
                  violation = false,
                ),
              stemTrace.actions.getOrNull(it)?.toSegment(inputFile),
            )
          }
          .map { ContentItem(it) } +
          (0..<(lassoTrace.length()))
            .flatMap {
              listOfNotNull(
                lassoTrace.states
                  .get(it)
                  ?.toSegment(
                    lassoTrace.actions.getOrNull(it - 1),
                    lassoTrace.actions.getOrNull(it),
                    inputFile,
                    Action.CYCLE,
                    parseContext = parseContext,
                  ),
                lassoTrace.actions.getOrNull(it)?.toSegment(inputFile, Action.CYCLE),
              )
            }
            .ifEmpty {
              val lastLoc =
                lassoTrace.actions
                  .flatMap { it.edge?.getFlatLabels() ?: listOf() }
                  .reversed()
                  .first { it.metadata.isSubstantial() }
              listOf(
                WaypointContent(
                  WaypointType.ASSUMPTION,
                  Constraint("1", Format.C_EXPRESSION),
                  Location(
                    fileName = inputFile.name,
                    line = (lastLoc.metadata as? CMetaData)?.lineNumberStart ?: -1,
                    column = (lastLoc.metadata as? CMetaData)?.colNumberStart?.plus(1) ?: -1,
                  ),
                  Action.CYCLE,
                )
              )
            }
            .map { ContentItem(it) },
    )
  }

  private fun reachabilityViolationWitnessFromConcreteTrace(
    concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
    metadata: Metadata,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
    functionReturnOnly: Boolean = false,
  ): YamlWitness {
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

  private fun violationWitnessFromConcreteTrace(
    concrTrace: Trace<XcfaState<ExplState>, XcfaAction>,
    metadata: Metadata,
    inputFile: File,
    property: XcfaProperty,
    parseContext: ParseContext,
    witnessfile: File,
  ): YamlWitness {
    val witness =
      if (property.inputProperty == ErrorDetection.TERMINATION) {
        terminationViolationWitnessFromConcreteTrace(
          concrTrace,
          metadata,
          inputFile,
          property,
          parseContext,
          witnessfile,
        )
      } else {
        reachabilityViolationWitnessFromConcreteTrace(
          concrTrace,
          metadata,
          inputFile,
          property,
          parseContext,
          witnessfile,
        )
      }
    return witness
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

private fun getStopLocation(inputFile: File, metadata: MetaData?): Location? {
  val line = (metadata as? CMetaData)?.lineNumberStop ?: return null
  val column = (metadata as? CMetaData)?.colNumberStop ?: return null
  return Location(fileName = inputFile.name, line = line, column = column?.plus(1))
}

private fun getLocation(inputFile: File, witnessEdge: WitnessEdge?): Location? {
  if (witnessEdge == null) return null
  val endLoc =
    Location(
      fileName = inputFile.name,
      line = witnessEdge.startline ?: witnessEdge.endline ?: return null,
      column = (witnessEdge.startcol ?: witnessEdge.endcol)?.plus(1),
    )
  return endLoc
}

var prevVal: Map<Decl<*>, LitExpr<*>> = emptyMap()

private fun WitnessNode.toSegment(
  incomingEdge: WitnessEdge?,
  outgoingEdge: WitnessEdge?,
  inputFile: File,
  action: Action = Action.FOLLOW,
  parseContext: ParseContext,
  violation: Boolean = false,
): WaypointContent? {
  var loc =
    Location(
      fileName = inputFile.name,
      line = outgoingEdge?.startline ?: -1,
      column = outgoingEdge?.startcol?.plus(1),
    )
  if (violation) {
    if (loc.line == -1) {
      val locLoc = xcfaLocations.values.first().first()
      loc =
        getLocation(inputFile, locLoc.metadata)
          ?: getLocation(inputFile, incomingEdge)
          ?: getLocation(inputFile, incomingEdge?.edge?.metadata)
          ?: return null
    }
    return WaypointContent(type = WaypointType.TARGET, location = loc, action = action)
  } else if (outgoingEdge?.startline != null && outgoingEdge.startcol != null) {
    // TODO this will very much break if we have 1+ nondet call on the edge or 1+ variable or .....
    if (
      (outgoingEdge.edge?.metadata as CMetaData).astNodes.any {
        it is CCall && it.functionId.contains("__VERIFIER_nondet_")
      } &&
        outgoingEdge.edge?.label is SequenceLabel &&
        (outgoingEdge.edge?.label as SequenceLabel).labels.any {
          it is StmtLabel && it.stmt is HavocStmt<*>
        }
    ) {
      val varsOnEdge = (outgoingEdge.edge?.label as SequenceLabel).collectVars().toSet()
      check(varsOnEdge.size == 1) // this has to be the havoced variable
      val varOnEdge = varsOnEdge.first()
      val typeName = CComplexType.getType(varOnEdge.ref, parseContext)?.typeName
      val assignedValue = outgoingEdge.target.globalState?.`val`!!.toMap()[varOnEdge] ?: return null
      val (cast, valueString) =
        if (assignedValue is BvLitExpr) "" to assignedValue.toString().replace("#", "0")
        else if (assignedValue is FpLitExpr)
          (typeName?.let { "($it)" } ?: "") to
            FpUtils.fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), assignedValue)
              .toString()
        else "" to assignedValue.toString()

      val constraint = "\\result == $cast$valueString"
      loc = getStopLocation(inputFile, outgoingEdge.edge?.metadata) ?: return null
      return WaypointContent(
        type = WaypointType.FUNCTION_RETURN,
        location = loc,
        action = action,
        constraint = Constraint(constraint, Format.C_EXPRESSION),
      )
    } else if ((outgoingEdge.edge?.metadata as CMetaData).astNodes.any { it is CIf }) {
      val constraintValue =
        if ((outgoingEdge.edge!!.label as StmtLabel).choiceType == ChoiceType.ALTERNATIVE_PATH)
          "false"
        else "true"
      return WaypointContent(
        type = WaypointType.BRANCHING,
        location = loc,
        action = action,
        constraint = Constraint(constraintValue, format = Format.C_EXPRESSION),
      )
    } else {
      // we only want assumptions that are actually about something in a function
      if ((outgoingEdge.edge!!.metadata as CMetaData).functionName != "notC") {
        return null
      } else {
        val constraint =
          globalState
            ?.toMap()
            ?.filter { (varDecl, value) -> !(prevVal[varDecl]?.equals(value) ?: false) }
            ?.mapNotNull { (varDecl, value) ->
              val splitName = varDecl.name.split("::")
              val rootName =
                if (splitName[0].matches(Regex("T[0-9]*")))
                  splitName.subList(2, splitName.size).joinToString("::")
                else varDecl.name
              if (
                splitName[splitName.size - 2] !=
                  (outgoingEdge.edge!!.metadata as CMetaData).functionName
              ) {
                null
              } else {
                if (parseContext.metadata.getMetadataValue(rootName, "cName").isPresent) {
                  "(${parseContext.metadata.getMetadataValue(rootName, "cName").get()} == ${
                    printLit(value)
                  })"
                } else {
                  null
                }
              }
            }
            ?.joinToString("&&")
            ?.let { if (it.isEmpty()) "1" else it }
        prevVal = globalState?.toMap() ?: prevVal

        return if (constraint != null && constraint.isNotEmpty()) {
          WaypointContent(
            type = WaypointType.ASSUMPTION,
            location = loc,
            action = action,
            constraint = Constraint(constraint, format = Format.C_EXPRESSION),
          )
        } else {
          null
        }
      }
    }
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
      return null
    } else if (control != null) {
      // Triple(startLoc, Constraint(value = control.toString()), WaypointType.BRANCHING)
      return null
    } else if (enterLoopHead) {
      // Triple(startLoc, Constraint(value = "true"), WaypointType.BRANCHING)
      return null
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
