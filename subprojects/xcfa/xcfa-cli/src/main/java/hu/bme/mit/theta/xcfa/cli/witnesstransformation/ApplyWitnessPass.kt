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
package hu.bme.mit.theta.xcfa.cli.witnesstransformation

import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.getExpressionFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs.Ite
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.statements.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.*
import java.util.*
import kotlin.jvm.optionals.getOrNull

/**
 * Instruments the XCFA with the constraints of a YAML witness.
 *
 * For violation witnesses, the segments of the witness are tracked by a segment counter: whenever
 * the program passes the location of the waypoint of the currently active segment (and its
 * constraint holds there), the counter advances; the violation (e.g., the error location) is only
 * accepted once the final segment has been passed.
 *
 * Multi-threaded programs are supported (witness format 2.2):
 * - The segment counter and flag are *global* variables, so the segment sequence is a cross-thread
 *   (happens-before) order: a waypoint of thread B in segment i+1 can only be passed once the
 *   waypoint of thread A in segment i has been. They are also *atomic*, so the instrumentation
 *   itself can never introduce a data race (which would break `no-data-race` validation).
 * - The pass is applied to every procedure; each waypoint is instrumented in the procedure(s) where
 *   its location matches. A waypoint carrying a `thread_id` is only applied in the procedure that
 *   the denoted thread executes (thread 0 is the entry procedure; thread k is registered by the
 *   k-th `function_enter` waypoint of the witness that sits on a thread-creating call, i.e., an
 *   edge with a [StartLabel]).
 * - All waypoints of a *multi-follow segment* (e.g., the two racing accesses that form the target
 *   of a `no-data-race` witness) share a single segment index, so no ordering -- and hence no
 *   happens-before edge -- is introduced among them: ordering the racing pair would remove the very
 *   race the witness exhibits.
 */
class ApplyWitnessPass(val parseContext: ParseContext, val witness: YamlWitness) : ProcedurePass {

  private data class Instrumentation(
    val segmentCounter: VarDecl<IntType>,
    val segmentFlag: VarDecl<BoolType>,
    /** thread_id (0 = entry procedure) -> name of the procedure the thread executes */
    val threadProcedures: Map<Int, String>,
  )

  companion object {

    const val SEGMENT_COUNTER = "__THETA__segment__counter__"
    const val LAST_SEGMENT_PASSED = "__THETA__last__segment__passed__"

    /**
     * State shared between the per-procedure runs of this pass (each procedure builder has its own
     * pass manager and thus its own pass instance): every procedure must refer to the very same
     * counter/flag [VarDecl]s, and the thread registry is global to the witness.
     */
    private val instrumentations = mutableMapOf<XcfaBuilder, Instrumentation>()
  }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    return if (witness.entryType == EntryType.VIOLATION) {
      applyViolationWitness(builder)
    } else {
      applyCorrectnessWitness(builder)
    }
  }

  private fun applyCorrectnessWitness(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val statementToEdge = getStatementToEdge(builder)
    val edgeToLabels =
      mutableMapOf<
        XcfaEdge,
        MutableMap<XcfaLabel, MutableSet<Expr<BoolType>>>,
        >() // on which edges, which labels must have these new assumptions beforehand.
    for (item in witness.content) {
      item.invariant?.let {
        val loc = it.location
        val labelsOnEdges =
          statementToEdge
            .filter { (statement, _, _) ->
              statement.lineNumberStart == loc.line &&
                (loc.column?.let { statement.colNumberStart + 1 == it } ?: true)
            }
            .map { (_, label, edge) -> Pair(label, edge) }
        if (labelsOnEdges.isEmpty()) {
          // the invariant's location is in some other procedure
          return@let
        }
        val inv =
          getExpressionFromC(
            it.value,
            parseContext,
            false,
            false,
            NullLogger.getInstance(),
            builder.getVars() + builder.parent.getVars().map { it.wrappedVar },
          )
        for ((label, edge) in labelsOnEdges) {
          edgeToLabels
            .computeIfAbsent(edge) { mutableMapOf() }
            .computeIfAbsent(label) { mutableSetOf() }
            .add(inv)
        }
      }
    }

    for ((edge, labels) in edgeToLabels) {
      builder.removeEdge(edge)
      val oldLabels = edge.getFlatLabels()
      val labelCollector = mutableListOf<XcfaLabel>()
      var i = 0
      var nextSource = edge.source
      builder.createErrorLoc()

      fun flush(last: Boolean = false) {
        if (labelCollector.isNotEmpty()) {
          val anonymLoc =
            if (last) edge.target
            else XcfaLocation("__tmp" + XcfaLocation.uniqueCounter(), metadata = EmptyMetaData)
          builder.addEdge(
            XcfaEdge(
              nextSource,
              anonymLoc,
              // copy the collector: edges hash their labels, so the label list must not be
              // mutated once the edge has been added
              label = SequenceLabel(labelCollector.toList()),
              metadata = EmptyMetaData,
            )
          )
          nextSource = anonymLoc
          labelCollector.clear()
        }
      }
      for ((label, assumptions) in labels) {
        while (i < oldLabels.indexOf(label)) {
          labelCollector.add(oldLabels[i])
          ++i
        }
        flush()
        builder.addEdge(
          XcfaEdge(
            nextSource,
            builder.errorLoc.get(),
            SequenceLabel(listOf(StmtLabel(AssumeStmt.of(Not(And(assumptions)))))),
            metadata = EmptyMetaData,
          )
        )
        labelCollector.add(StmtLabel(AssumeStmt.of(And(assumptions))))
      }
      while (i < oldLabels.size) {
        labelCollector.add(oldLabels[i])
        ++i
      }
      flush(true)
    }

    return builder
  }

  private fun applyViolationWitness(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val instrumentation =
      instrumentations.computeIfAbsent(builder.parent) { createInstrumentation(it) }
    val segmentCounter = instrumentation.segmentCounter
    val segmentFlag = instrumentation.segmentFlag

    val segments = witness.content.mapNotNull { c -> c.segment }
    val segmentCount = segments.size

    // The counter and flag come to life when the program (i.e., the entry procedure) starts;
    // spawned threads only run after that.
    if (builder.parent.getInitProcedures().any { it.first.name == builder.name }) {
      for (outgoingEdge in builder.initLoc.outgoingEdges.toSet()) {
        builder.removeEdge(outgoingEdge)
        val intermediateLoc =
          XcfaLocation("__loc_witness_" + XcfaLocation.uniqueCounter(), metadata = outgoingEdge.metadata)
        val annotationEdge = XcfaEdge(
          outgoingEdge.source, intermediateLoc, SequenceLabel(
            listOf(
              AssignStmtLabel(segmentCounter, Int(0)),
              AssignStmtLabel(segmentFlag, False()),
            )
          ), outgoingEdge.metadata
        )
        builder.addEdge(annotationEdge)
        builder.addEdge(outgoingEdge.withSource(intermediateLoc))
      }
    }

    val modifications = LinkedHashMap<XcfaEdge, MutableList<Annotation>>()

    var firstCycle = -1
    val statementToEdge = getStatementToEdge(builder)
    segments.forEachIndexed { segmentIndex, segment ->
      val currentSegmentPred = Eq(segmentCounter.ref, Int(segmentIndex))
      // All (non-avoid) waypoints of the segment share the segment index: in a multi-follow
      // segment (e.g., the racing pair of a no-data-race witness) this leaves the waypoints
      // mutually unordered.
      val waypoints = segment.filter { waypoint -> waypoint.waypoint.action != Action.AVOID }
      if (firstCycle == -1 && waypoints.any { it.waypoint.action == Action.CYCLE }) {
        firstCycle = segmentIndex
      }

      val isLastSegment = segmentIndex == segmentCount - 1
      val segmentUpdate =
        if (isLastSegment && firstCycle > -1) {
          Pair(currentSegmentPred, Int(firstCycle))
        } else if (!isLastSegment) {
          Pair(currentSegmentPred, Int(segmentIndex + 1))
        } else {
          null
        }

      val segmentFlagUpdate =
        if (isLastSegment) {
          AssignStmtLabel(segmentFlag, Ite(currentSegmentPred, True(), segmentFlag.ref))
        } else null

      for (wp in waypoints) {
        if (!mayExecuteInProcedure(wp.waypoint, builder, instrumentation)) continue
        val loc = wp.waypoint.location

        val labelsOnEdges =
          statementToEdge
            .filter { (statement, label, _) ->
              if (wp.waypoint.type == WaypointType.FUNCTION_RETURN) {
                statement.lineNumberStart == loc.line &&
                  (loc.column == null ||
                    statement.colNumberStop + 1 - 1 == loc.column ||
                    statement.colNumberStop + 1 == loc.column) &&
                  label is StmtLabel &&
                  label.stmt is HavocStmt<*>
              } else {
                statement.lineNumberStart == loc.line &&
                  (loc.column == null || statement.colNumberStart + 1 == loc.column)
              }
            }
            .map { (_, label, edge) -> Pair(label, edge) }
        if (labelsOnEdges.isEmpty()) {
          // The waypoint's location is not in this procedure (e.g., it belongs to another
          // thread's code); it is instrumented wherever it matches.
          continue
        }

        val expr =
          Imply(currentSegmentPred, waypointConstraint(wp.waypoint, statementToEdge, builder))
        val assumption = StmtLabel(AssumeStmt.of(expr), ChoiceType.NONE, EmptyMetaData)

        val edgeLabels = LinkedHashMap<XcfaEdge, MutableList<XcfaLabel>>()
        for ((label, edge) in labelsOnEdges) {
          edgeLabels.computeIfAbsent(edge) { LinkedList() }.add(label)
        }

        for ((edge, labels) in edgeLabels) {
          val oldLabels = edge.getFlatLabels()
          val annotatedLabels =
            labels
              .map { label ->
                oldLabels.indexOf(label) +
                  if (wp.waypoint.type == WaypointType.FUNCTION_RETURN) 1
                  else 0 // for function_return, we want to add it next.
              }
              .sorted()
              .map { oldLabels[it] }
          for (label in annotatedLabels) {
            modifications
              .computeIfAbsent(edge) { LinkedList() }
              .add(
                Annotation(
                  edge,
                  label,
                  assumption,
                  segmentUpdate,
                  segmentFlagUpdate,
                )
              )
          }
        }
      }
    }

    modifications.forEach { (edge, allAnnots) ->
      builder.removeEdge(edge)
      val oldLabels = edge.getFlatLabels()
      var newLabels = LinkedList<XcfaLabel>()
      val indexToAnnots =
        allAnnots.groupBy { oldLabels.indexOf(it.beforeLabel) }.toList().sortedBy { it.first }
      var i = 0

      var lastLoc = edge.source
      var lastNewLabelsSize = 0
      val flushLabels = { target: XcfaLocation, flushAnyway: Boolean ->
        if (flushAnyway) {
          val newEdge = XcfaEdge(lastLoc, target, SequenceLabel(newLabels), edge.metadata)
          builder.addEdge(newEdge)
          lastLoc = target
          newLabels = LinkedList()
        } else {
          val newSlice = newLabels.safeSlice(lastNewLabelsSize..newLabels.size)
          if (newSlice.any { it is StartLabel || it is JoinLabel || it is FenceLabel }) {
            val previousSlice = newLabels.safeSlice(0 until lastNewLabelsSize)
            var source = lastLoc
            if (previousSlice.isNotEmpty()) {
              val loc = XcfaLocation("__loc_witness_" + XcfaLocation.uniqueCounter(), metadata = edge.label.metadata)
              val newEdge = XcfaEdge(source, loc, SequenceLabel(previousSlice), edge.metadata)
              builder.addEdge(newEdge)
              source = loc
            }
            val newEdge = XcfaEdge(source, target, SequenceLabel(newSlice), edge.metadata)
            builder.addEdge(newEdge)
            lastLoc = target
            newLabels = LinkedList()
          }
        }
        lastNewLabelsSize = newLabels.size
      }

      val flushLabelsIntermediate = {
        val loc = XcfaLocation("__loc_witness_" + XcfaLocation.uniqueCounter(), metadata = edge.label.metadata)
        flushLabels(loc, false)
      }

      // assumptions first (to keep assumptions at the beginning for branching)
      while (i < oldLabels.size) {
        if (oldLabels[i] is StmtLabel && (oldLabels[i] as StmtLabel).stmt is AssumeStmt) {
          newLabels.add(oldLabels[i])
          i++
        } else break
      }
      flushLabelsIntermediate()

      for ((index, annots) in indexToAnnots) {
        while (i < index) {
          newLabels.add(oldLabels[i++])
        }
        flushLabelsIntermediate()

        newLabels.addAll(annots.map { it.assumption })
        newLabels.addAll(annots.mapNotNull { it.flagUpdate })
        var expr = segmentCounter.ref as Expr<IntType>
        for ((cond, then) in annots.mapNotNull { it.segmentUpdate }) {
          expr = Ite(cond, then, expr)
        }
        newLabels.add(AssignStmtLabel(segmentCounter, expr))

        flushLabelsIntermediate()
      }
      while (i < oldLabels.size) {
        newLabels.add(oldLabels[i++])
      }

      flushLabels(edge.target, true)
    }

    if (firstCycle == -1) { // we are checking reachability, TODO refactor
      // The violation is only accepted after the full segment sequence has been passed; this
      // gates the error location of every procedure (the target may be in a spawned thread).
      builder.errorLoc.getOrNull()?.incomingEdges?.toSet()?.forEach {
        builder.removeEdge(it)
        builder.addEdge(
          it.withLabel(
            SequenceLabel(
              it.getFlatLabels() + StmtLabel(AssumeStmt.of(segmentFlag.ref)),
              metadata = it.label.metadata,
            )
          )
        )
      }
    }

    builder.prop = segmentFlag.ref
    return builder
  }

  /** The constraint that has to hold when the waypoint is passed. */
  private fun waypointConstraint(
    wp: WaypointContent,
    statementToEdge: LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>,
    builder: XcfaProcedureBuilder,
  ): Expr<BoolType> {
    val loc = wp.location
    return when (wp.type) {
      WaypointType.ASSUMPTION -> {
        val constraint = wp.constraint!!
        check(
          constraint.format!! == Format.C_EXPRESSION ||
            constraint.format!! == Format.EXT_C_EXPRESSION
        ) {
          "Not handled: $constraint"
        }
        getExpressionFromC(
          constraint.value,
          parseContext,
          false,
          false,
          NullLogger.getInstance(),
          builder.getVars() + builder.parent.getVars().map { it.wrappedVar },
        )
      }

      WaypointType.FUNCTION_RETURN -> {
        val vars =
          statementToEdge
            .filter { (statement, label, _) ->
              statement.lineNumberStart == loc.line &&
                (loc.column == null ||
                  statement.colNumberStop + 1 - 1 == loc.column ||
                  statement.colNumberStop + 1 == loc.column) &&
                label is StmtLabel &&
                label.stmt is HavocStmt<*>
            }
            .map { (_, label, _) -> ((label as StmtLabel).stmt as HavocStmt<*>).varDecl }

        if (vars.size != 1) {
          True() // no or multiple vars
        } else {
          val v = vars.first()
          val cNameOpt = parseContext.metadata.getMetadataValue(v.name, "cName")
          if (cNameOpt.isPresent) {
            val constraint = wp.constraint!!
            check(
              constraint.format!! == Format.C_EXPRESSION ||
                constraint.format!! == Format.EXT_C_EXPRESSION
            ) {
              "Not handled: $constraint"
            }
            getExpressionFromC(
              constraint.value.replace("\\result", cNameOpt.get() as String),
              parseContext,
              false,
              false,
              NullLogger.getInstance(),
              builder.getVars() + builder.parent.getVars().map { it.wrappedVar },
            )
          } else {
            True() // no cname
          }
        }
      }

      WaypointType.BRANCHING -> {
        val branching =
          statementToEdge
            .mapNotNull { (statement, _, _) ->
              if (
                statement.lineNumberStart == loc.line &&
                (loc.column == null || statement.colNumberStart + 1 == loc.column)
              )
                statement
              else null
            }
            .firstOrNull { it is CWhile || it is CFor || it is CIf || it is CDoWhile } // we hope it's a single ast node..
            ?: error("Branching not on iteration/branching statement.")

        val guardAssume =
          statementToEdge.mapNotNull {
            if (
              it.first == branching &&
              it.second is StmtLabel &&
              (it.second as StmtLabel).stmt is AssumeStmt &&
              (it.second as StmtLabel).choiceType != ChoiceType.NONE
            )
              Pair((it.second as StmtLabel).choiceType, (it.second as StmtLabel).stmt as AssumeStmt)
            else null
          }

        when (wp.constraint?.value) {
          "true" -> {
            guardAssume.first { it.first == ChoiceType.MAIN_PATH }.second.cond
          }

          "false" -> {
            guardAssume.first { it.first == ChoiceType.ALTERNATIVE_PATH }.second.cond
          }

          else -> {
            error("Unknown value for branching: ${wp.constraint?.value}")
          }
        }
      }

      WaypointType.FUNCTION_ENTER,
      WaypointType.TARGET -> {
        // no-op now
        True()
      }
    }
  }

  /**
   * Waypoints carrying a `thread_id` are only applied in the procedure that the denoted thread
   * executes. The filter only disambiguates among the *known* thread root procedures: a waypoint is
   * never excluded from a procedure outside the registry (e.g., a function that could not be
   * inlined), and waypoints without a (resolvable) `thread_id` are applied wherever their location
   * matches.
   */
  private fun mayExecuteInProcedure(
    wp: WaypointContent,
    builder: XcfaProcedureBuilder,
    instrumentation: Instrumentation,
  ): Boolean {
    val threadId = wp.threadId ?: return true
    val procedureName = instrumentation.threadProcedures[threadId] ?: return true
    return procedureName == builder.name || builder.name !in instrumentation.threadProcedures.values
  }

  private fun createInstrumentation(parent: XcfaBuilder): Instrumentation {
    val segmentCounter = Var(SEGMENT_COUNTER, Int())
    val segmentFlag = Var(LAST_SEGMENT_PASSED, Bool())
    // Global: waypoints of different threads must see the same segment progression.
    // Atomic: the instrumentation itself must never introduce a data race -- a non-atomic
    // counter would make every pair of instrumented edges a (spurious) race, breaking the
    // validation of no-data-race witnesses.
    parent.addVar(XcfaGlobalVar(segmentCounter, Int(0), atomic = true))
    parent.addVar(XcfaGlobalVar(segmentFlag, False(), atomic = true))
    return Instrumentation(segmentCounter, segmentFlag, mapThreadsToProcedures(parent))
  }

  /**
   * Maps the `thread_id`s of the witness to procedure names: thread 0 is the entry procedure, and
   * the k-th thread-registering `function_enter` waypoint of the witness -- one whose location is a
   * thread-creating call, i.e., a statement carrying a [StartLabel] -- registers thread k with the
   * procedure started there. If the witness references `thread_id`s beyond the registrations found
   * this way, the numbering cannot be trusted, and no thread-based filtering is performed (an empty
   * registry is returned): waypoints are then matched by location only, which over-approximates the
   * witness but stays sound.
   */
  private fun mapThreadsToProcedures(parent: XcfaBuilder): Map<Int, String> {
    val startedProcedures =
      parent.getProcedures().flatMap { procedure ->
        getStatementToEdge(procedure).mapNotNull { (statement, label, _) ->
          if (label is StartLabel) Pair(statement.lineNumberStart, label.name) else null
        }
      }

    val threadProcedures = mutableMapOf<Int, String>()
    parent.getInitProcedures().firstOrNull()?.let { threadProcedures[0] = it.first.name }
    var nextThreadId = 1
    for (item in witness.content) {
      for (waypoint in item.segment ?: continue) {
        val wp = waypoint.waypoint
        if (wp.type == WaypointType.FUNCTION_ENTER && wp.action != Action.AVOID) {
          val started = startedProcedures.firstOrNull { it.first == wp.location.line }?.second
          if (started != null) {
            threadProcedures[nextThreadId++] = started
          }
        }
      }
    }

    val maxUsedThreadId =
      witness.content
        .flatMap { it.segment ?: emptyList() }
        .mapNotNull { it.waypoint.threadId }
        .maxOrNull() ?: 0
    return if (maxUsedThreadId >= nextThreadId) emptyMap() else threadProcedures
  }
}

fun getStatementToEdge(
  builder: XcfaProcedureBuilder
): LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>> {
  val statementToEdge = LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>()
  for (edge in builder.getEdges()) {
    extractEdge(edge, statementToEdge)
  }
  return statementToEdge
}

private fun extractEdge(
  edge: XcfaEdge,
  statementToEdge: LinkedHashSet<Triple<CStatement, XcfaLabel, XcfaEdge>>,
) {
  for (flatLabel in edge.label.getFlatLabels()) {
    (flatLabel.metadata as? CMetaData)?.also {
      for (astNode in it.astNodes) {
        statementToEdge.add(Triple(astNode, flatLabel, edge))
        // for termination, we also need iteration statements' bodies
        //        if (astNode is CWhile) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        } else if (astNode is CFor) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        } else if (astNode is CDoWhile) {
        //          statementToEdge.add(Triple(astNode.body, flatLabel, edge))
        //        }
      }
    }
  }
}

fun <T> List<T>.safeSlice(range: IntRange): List<T> =
  drop(range.first).take(range.last - range.first + 1)


private data class Annotation(
  val edge: XcfaEdge,
  val beforeLabel: XcfaLabel,
  val assumption: XcfaLabel,
  val segmentUpdate: Pair<Expr<BoolType>, Expr<IntType>>?,
  val flagUpdate: XcfaLabel?,
)
