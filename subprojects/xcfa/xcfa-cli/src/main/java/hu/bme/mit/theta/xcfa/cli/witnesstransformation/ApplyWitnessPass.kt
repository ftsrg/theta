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
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.LAST_SEGMENT_PASSED
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.LOGICAL_THREAD_ID
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.SEGMENT_COUNTER
import hu.bme.mit.theta.xcfa.ThetaHelperDeclarations.Witness.THREAD_ID_PARAM
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
 * - On top of the *static* (per-procedure) filtering above, the segments are guarded by a *runtime*
 *   logical thread id, so an instrumented thread instance only advances a segment if it is the very
 *   thread the witness refers to (this matters when the same procedure runs as several threads, or
 *   when a thread-creating call is visited several times). The logical id lives in a per-thread
 *   variable [LOGICAL_THREAD_ID] (the entry thread is `0`); a spawned thread receives its id
 *   through an extra [StartLabel] parameter and stores it on entry. A thread-creating
 *   `function_enter` waypoint hands the spawned thread the next logical id `k` only while its
 *   segment is the current one and the spawning thread is the right one; otherwise the spawned
 *   thread gets [INVALID_THREAD_ID] and can match no `thread_id`. Every waypoint then advances its
 *   segment only when both the segment counter *and* the logical thread id match.
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
    /** the thread-creating `function_enter` waypoints, in registration (witness) order */
    val registrations: List<ThreadRegistration>,
  )

  /**
   * A single thread registration: the k-th thread-creating `function_enter` waypoint of the witness
   * assigns logical [threadId] `k` to the thread spawned at [locationLine] (running
   * [startedProcedure]). The registration is only effective while the segment counter sits on
   * [segmentIndex] and the spawning thread is the one named by [parentThreadId] (the `thread_id` of
   * the `function_enter` waypoint itself).
   */
  private data class ThreadRegistration(
    val threadId: Int,
    val segmentIndex: Int,
    val locationLine: Int,
    val startedProcedure: String,
    val parentThreadId: Int?,
  )

  companion object {

    /** Logical id handed to a thread spawned outside of (or not registered by) the witness. */
    const val INVALID_THREAD_ID = -1

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
    // The first segment that carries a `cycle` waypoint; -1 if the witness is acyclic. Used both
    // here and by the thread-registration step to wrap the segment counter around at the end.
    val firstCycle = segments.indexOfFirst { seg -> seg.any { it.waypoint.action == Action.CYCLE } }

    // Logical thread ids are only tracked when the witness thread numbering could be resolved.
    val threadingEnabled = instrumentation.threadProcedures.isNotEmpty()
    val isEntry = builder.parent.getInitProcedures().any { it.first.name == builder.name }
    val isThreadRoot =
      builder.name in instrumentation.threadProcedures.filterKeys { it != 0 }.values
    // The entry thread and spawned-thread roots are the only procedures whose logical id is set;
    // everywhere else (e.g. a non-inlined callee) we fall back to segment-only guarding.
    val hasTid = threadingEnabled && (isEntry || isThreadRoot)
    val logicalThreadId: VarDecl<IntType>? =
      if (hasTid) Var(LOGICAL_THREAD_ID, Int()).also { builder.addVar(it) } else null

    // A spawned thread receives its logical id through an extra StartLabel parameter (added by
    // registerThreads in the spawning procedure) and stores it into its per-thread id variable
    // right after entry.
    if (isThreadRoot && logicalThreadId != null) {
      val tidParam = Var(THREAD_ID_PARAM, Int())
      builder.addParam(tidParam, ParamDirection.IN)
      for (outgoingEdge in builder.initLoc.outgoingEdges.toSet()) {
        builder.removeEdge(outgoingEdge)
        val intermediateLoc =
          XcfaLocation(
            "__loc_witness_" + XcfaLocation.uniqueCounter(),
            metadata = outgoingEdge.metadata,
          )
        builder.addEdge(
          XcfaEdge(
            outgoingEdge.source,
            intermediateLoc,
            SequenceLabel(listOf(AssignStmtLabel(logicalThreadId, tidParam.ref))),
            outgoingEdge.metadata,
          )
        )
        builder.addEdge(outgoingEdge.withSource(intermediateLoc))
      }
    }

    // The counter and flag come to life when the program (i.e., the entry procedure) starts;
    // spawned threads only run after that. The entry thread also fixes its own logical id to 0.
    if (isEntry) {
      for (outgoingEdge in builder.initLoc.outgoingEdges.toSet()) {
        builder.removeEdge(outgoingEdge)
        val intermediateLoc =
          XcfaLocation(
            "__loc_witness_" + XcfaLocation.uniqueCounter(),
            metadata = outgoingEdge.metadata,
          )
        val initLabels =
          mutableListOf<XcfaLabel>(
            AssignStmtLabel(segmentCounter, Int(0)),
            AssignStmtLabel(segmentFlag, False()),
          )
        if (logicalThreadId != null) initLabels.add(AssignStmtLabel(logicalThreadId, Int(0)))
        builder.addEdge(
          XcfaEdge(
            outgoingEdge.source,
            intermediateLoc,
            SequenceLabel(initLabels),
            outgoingEdge.metadata,
          )
        )
        builder.addEdge(outgoingEdge.withSource(intermediateLoc))
      }
    }

    // Hand out logical ids and advance segments at the thread-creating StartLabels of this
    // procedure (the matching `function_enter` waypoints are therefore skipped below).
    if (threadingEnabled) {
      registerThreads(builder, instrumentation, logicalThreadId, hasTid, segmentCount, firstCycle)
    }

    val modifications = LinkedHashMap<XcfaEdge, MutableList<Annotation>>()

    val statementToEdge = getStatementToEdge(builder)
    segments.forEachIndexed { segmentIndex, segment ->
      val currentSegmentPred = Eq(segmentCounter.ref, Int(segmentIndex))
      // All (non-avoid) waypoints of the segment share the segment index: in a multi-follow
      // segment (e.g., the racing pair of a no-data-race witness) this leaves the waypoints
      // mutually unordered.
      val waypoints = segment.filter { waypoint -> waypoint.waypoint.action != Action.AVOID }

      val isLastSegment = segmentIndex == segmentCount - 1

      for (wp in waypoints) {
        // Thread-creating function_enter waypoints are handled by registerThreads.
        if (
          threadingEnabled &&
            wp.waypoint.type == WaypointType.FUNCTION_ENTER &&
            isThreadRegistration(instrumentation, wp.waypoint, segmentIndex)
        )
          continue
        if (!mayExecuteInProcedure(wp.waypoint, builder, instrumentation)) continue
        val loc = wp.waypoint.location

        // The segment is only passed once the counter is on it AND the executing thread is the one
        // the waypoint names; this per-waypoint guard replaces the plain segment predicate.
        val guardPred =
          threadGuard(currentSegmentPred, wp.waypoint.threadId, hasTid, logicalThreadId)
        val segmentUpdate =
          if (isLastSegment && firstCycle > -1) {
            Pair(guardPred, Int(firstCycle))
          } else if (!isLastSegment) {
            Pair(guardPred, Int(segmentIndex + 1))
          } else {
            null
          }
        val segmentFlagUpdate =
          if (isLastSegment) {
            AssignStmtLabel(segmentFlag, Ite(guardPred, True(), segmentFlag.ref))
          } else null

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

        val expr = Imply(guardPred, waypointConstraint(wp.waypoint, statementToEdge, builder))
        val assumption = StmtLabel(AssumeStmt.of(expr), ChoiceType.NONE, EmptyMetaData)

        val edgeLabels = LinkedHashMap<XcfaEdge, MutableSet<XcfaLabel>>()
        for ((label, edge) in labelsOnEdges) {
          edgeLabels.computeIfAbsent(edge) { LinkedHashSet() }.add(label)
        }

        for ((edge, matchedLabels) in edgeLabels) {
          val oldLabels = edge.getFlatLabels()
          // Instrument *every* occurrence of a matched label on the edge. Inlining places several
          // structurally identical labels (same statement and metadata) on one edge -- e.g. the
          // three inlined copies of f()'s `return` all look the same -- and the witness carries a
          // separate segment for each visit. Each occurrence must get the guarded check/advance so
          // the counter is updated whenever that location is reached (the ITE guards let only the
          // matching segment fire). Indexing by label (indexOf) would instead collapse every
          // occurrence onto the first, leaving later visits uninstrumented and stalling the
          // sequence.
          val annotatedIndices =
            oldLabels.indices
              .filter { oldLabels[it] in matchedLabels }
              .map { it + if (wp.waypoint.type == WaypointType.FUNCTION_RETURN) 1 else 0 }
              .sorted()
          for (index in annotatedIndices) {
            modifications
              .computeIfAbsent(edge) { LinkedList() }
              .add(Annotation(edge, index, assumption, segmentUpdate, segmentFlagUpdate))
          }
        }
      }
    }

    modifications.forEach { (edge, allAnnots) ->
      builder.removeEdge(edge)
      val oldLabels = edge.getFlatLabels()
      var newLabels = LinkedList<XcfaLabel>()
      val indexToAnnots = allAnnots.groupBy { it.beforeIndex }.toList().sortedBy { it.first }
      var i = 0

      var lastLoc = edge.source
      var lastNewLabelsSize = 0
      val flushLabels = { target: XcfaLocation, flushAnyway: Boolean ->
        val newSlice = newLabels.safeSlice(lastNewLabelsSize..newLabels.size)
        if (
          flushAnyway || newSlice.any { it is StartLabel || it is JoinLabel || it is FenceLabel }
        ) {
          val previousSlice = newLabels.safeSlice(0 until lastNewLabelsSize)
          var source = lastLoc
          if (previousSlice.isNotEmpty()) {
            val loc =
              XcfaLocation(
                "__loc_witness_" + XcfaLocation.uniqueCounter(),
                metadata = edge.label.metadata,
              )
            val newEdge = XcfaEdge(source, loc, SequenceLabel(previousSlice), edge.metadata)
            builder.addEdge(newEdge)
            source = loc
          }
          val newEdge = XcfaEdge(source, target, SequenceLabel(newSlice), edge.metadata)
          builder.addEdge(newEdge)
          lastLoc = target
          newLabels = LinkedList()
        }
        lastNewLabelsSize = newLabels.size
      }

      val flushLabelsIntermediate = {
        val loc =
          XcfaLocation(
            "__loc_witness_" + XcfaLocation.uniqueCounter(),
            metadata = edge.label.metadata,
          )
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

        newLabels.addAll(annots.mapNotNull { if (it.assumption == AssumeStmt.of(True())) null else it.assumption })
        newLabels.addAll(annots.mapNotNull { it.flagUpdate })
        // Apply the segment-counter advances of this group sequentially, in segment order. When
        // several waypoints fall on the same edge position (e.g. a function_return immediately
        // followed by the next segment's assumption), each advance must see the counter value left
        // by the previous one, so the counter can step e.g. 1 -> 2 -> 3 within a single edge
        // traversal. Folding them into one nested-ite assignment instead lets only the first
        // matching guard fire (every guard is evaluated against the same pre-advance value), which
        // stalls the segment sequence and gates off the violation.
        for ((cond, then) in annots.mapNotNull { it.segmentUpdate }) {
          newLabels.add(AssignStmtLabel(segmentCounter, Ite(cond, then, segmentCounter.ref)))
        }

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

    // Loops are not unrolled here: the OC backend drives loop unrolling itself (incrementally and,
    // for witness validation, unboundedly), starting from the witness-implied depth set in
    // ConfigToOcChecker. Unrolling here as well would only duplicate that work -- and, for loops
    // containing an atomic block, produce ill-formed multi-instance atomic merges.

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
            .firstOrNull {
              it is CWhile || it is CFor || it is CIf || it is CDoWhile
            } // we hope it's a single ast node..
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

  /**
   * The runtime guard of a waypoint: the segment counter has to be on the waypoint's segment and --
   * when the logical thread id is being tracked in this procedure -- the executing thread has to be
   * the one named by the waypoint's `thread_id`.
   */
  private fun threadGuard(
    segmentPred: Expr<BoolType>,
    threadId: Int?,
    hasTid: Boolean,
    logicalThreadId: VarDecl<IntType>?,
  ): Expr<BoolType> =
    if (hasTid && threadId != null && logicalThreadId != null)
      And(segmentPred, Eq(logicalThreadId.ref, Int(threadId)))
    else segmentPred

  /** Whether [wp] is a thread-creating `function_enter` registered in [segmentIndex]. */
  private fun isThreadRegistration(
    instrumentation: Instrumentation,
    wp: WaypointContent,
    segmentIndex: Int,
  ): Boolean =
    instrumentation.registrations.any {
      it.segmentIndex == segmentIndex && it.locationLine == wp.location.line
    }

  /**
   * Augments every thread-creating [StartLabel] of [builder] so that the spawned thread receives a
   * logical id, and advances the segment counter when the corresponding `function_enter` waypoint
   * is passed. The id handed over is the registration index `k` while the registering segment is
   * the current one and the spawning thread matches; otherwise it is [INVALID_THREAD_ID]. A single
   * StartLabel may carry several registrations (e.g. a thread-creating call visited in several
   * segments), which are folded into a nested `ite`.
   */
  private fun registerThreads(
    builder: XcfaProcedureBuilder,
    instrumentation: Instrumentation,
    logicalThreadId: VarDecl<IntType>?,
    hasTid: Boolean,
    segmentCount: Int,
    firstCycle: Int,
  ) {
    val segmentCounter = instrumentation.segmentCounter
    val segmentFlag = instrumentation.segmentFlag
    val registeredRoots = instrumentation.threadProcedures.filterKeys { it != 0 }.values.toSet()
    if (registeredRoots.isEmpty()) return

    val startLabelLine =
      getStatementToEdge(builder)
        .mapNotNull { (statement, label, _) ->
          if (label is StartLabel) Pair(label, statement.lineNumberStart) else null
        }
        .toMap()

    fun parentGuard(reg: ThreadRegistration): Expr<BoolType> {
      val segPred = Eq(segmentCounter.ref, Int(reg.segmentIndex))
      return if (hasTid && reg.parentThreadId != null && logicalThreadId != null)
        And(segPred, Eq(logicalThreadId.ref, Int(reg.parentThreadId)))
      else segPred
    }

    for (edge in builder.getEdges().toSet()) {
      val flatLabels = edge.getFlatLabels()
      if (flatLabels.none { it is StartLabel && it.name in registeredRoots }) continue

      builder.removeEdge(edge)
      var source = edge.source
      val collector = mutableListOf<XcfaLabel>()

      fun cut() {
        val target =
          XcfaLocation("__loc_witness_" + XcfaLocation.uniqueCounter(), metadata = EmptyMetaData)
        builder.addEdge(XcfaEdge(source, target, SequenceLabel(collector.toList()), edge.metadata))
        source = target
        collector.clear()
      }

      for (label in flatLabels) {
        if (label is StartLabel && label.name in registeredRoots) {
          val line = startLabelLine[label]
          val regs =
            instrumentation.registrations.filter {
              it.startedProcedure == label.name && (line == null || it.locationLine == line)
            }
          val paramValue =
            regs.foldRight(Int(INVALID_THREAD_ID) as Expr<IntType>) { reg, acc ->
              Ite(parentGuard(reg), Int(reg.threadId), acc)
            }
          // The StartLabel (now carrying the logical id) must stay on its own edge, and the segment
          // counter must only advance afterwards (so the handed-over id sees the pre-advance
          // value).
          collector.add(label.copy(params = label.params + paramValue))
          cut()
          if (regs.isNotEmpty()) {
            var counterExpr = segmentCounter.ref as Expr<IntType>
            var flagExpr = segmentFlag.ref as Expr<BoolType>
            var anyFlag = false
            for (reg in regs) {
              val guard = parentGuard(reg)
              if (reg.segmentIndex == segmentCount - 1) {
                if (firstCycle > -1) counterExpr = Ite(guard, Int(firstCycle), counterExpr)
                flagExpr = Ite(guard, True(), flagExpr)
                anyFlag = true
              } else {
                counterExpr = Ite(guard, Int(reg.segmentIndex + 1), counterExpr)
              }
            }
            if (anyFlag) collector.add(AssignStmtLabel(segmentFlag, flagExpr))
            collector.add(AssignStmtLabel(segmentCounter, counterExpr))
            cut()
          }
        } else {
          collector.add(label)
        }
      }
      builder.addEdge(
        XcfaEdge(source, edge.target, SequenceLabel(collector.toList()), edge.metadata)
      )
    }
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
    val (threadProcedures, registrations) = mapThreads(parent)
    return Instrumentation(segmentCounter, segmentFlag, threadProcedures, registrations)
  }

  /**
   * Resolves the witness `thread_id`s. Thread 0 is the entry procedure, and the k-th
   * thread-registering `function_enter` waypoint -- one whose location is a thread-creating call,
   * i.e., a statement carrying a [StartLabel] -- registers thread k with the procedure started
   * there. Returns both the id -> procedure-name map and the per-registration details (segment,
   * spawning thread, ...) used to drive the runtime thread numbering. If the witness references
   * `thread_id`s beyond the registrations found this way, the numbering cannot be trusted and empty
   * results are returned: waypoints are then matched by location only, which over-approximates the
   * witness but stays sound.
   */
  private fun mapThreads(parent: XcfaBuilder): Pair<Map<Int, String>, List<ThreadRegistration>> {
    val startedProcedures =
      parent.getProcedures().flatMap { procedure ->
        getStatementToEdge(procedure).mapNotNull { (statement, label, _) ->
          if (label is StartLabel) Pair(statement.lineNumberStart, label.name) else null
        }
      }

    val segments = witness.content.mapNotNull { it.segment }
    val registrations = mutableListOf<ThreadRegistration>()
    var nextThreadId = 1
    segments.forEachIndexed { segmentIndex, segment ->
      for (waypoint in segment) {
        val wp = waypoint.waypoint
        if (wp.type == WaypointType.FUNCTION_ENTER && wp.action != Action.AVOID) {
          val started = startedProcedures.firstOrNull { it.first == wp.location.line }?.second
          if (started != null) {
            registrations.add(
              ThreadRegistration(
                nextThreadId++,
                segmentIndex,
                wp.location.line,
                started,
                wp.threadId,
              )
            )
          }
        }
      }
    }

    val threadProcedures = buildMap {
      parent.getInitProcedures().firstOrNull()?.let { put(0, it.first.name) }
      registrations.forEach { put(it.threadId, it.startedProcedure) }
    }

    val maxUsedThreadId = segments.flatten().mapNotNull { it.waypoint.threadId }.maxOrNull() ?: 0
    return if (maxUsedThreadId >= nextThreadId) Pair(emptyMap(), emptyList())
    else Pair(threadProcedures, registrations)
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
  /**
   * Position in `edge.getFlatLabels()` to insert before; an index (not a label) so that several
   * identical inlined occurrences of the same statement stay distinct.
   */
  val beforeIndex: Int,
  val assumption: XcfaLabel,
  val segmentUpdate: Pair<Expr<BoolType>, Expr<IntType>>?,
  val flagUpdate: XcfaLabel?,
)
