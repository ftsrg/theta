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
import hu.bme.mit.theta.c2xcfa.getBoolExpressionFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.Format
import hu.bme.mit.theta.xcfa.witnesses.Invariant
import hu.bme.mit.theta.xcfa.witnesses.InvariantCheck
import hu.bme.mit.theta.xcfa.witnesses.InvariantCheckMetaData
import hu.bme.mit.theta.xcfa.witnesses.InvariantType
import hu.bme.mit.theta.xcfa.witnesses.YamlWitness

/**
 * Prepares the validation of a termination correctness witness. Each evaluation point of its
 * invariants gets a location of its own, marked with [InvariantCheckMetaData], from which the
 * liveness-to-safety reduction checks them (see `XcfaSingleThreadToMonolithicAdapter`).
 *
 * Every invariant must have an evaluation point in the entry procedure, which holds the whole
 * program once it is inlined. A witness element that cannot be checked exactly fails the run.
 */
class TerminationWitnessPass(
  private val parseContext: ParseContext,
  private val witness: YamlWitness,
) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val isEntry = builder.parent.getInitProcedures().any { it.first.name == builder.name }
    // checks before the first label of an edge, and before a later label of it
    val atStart = LinkedHashMap<XcfaEdge, MutableList<InvariantCheck>>()
    val inside = LinkedHashMap<XcfaEdge, MutableMap<Int, MutableList<InvariantCheck>>>()
    witness.content.forEachIndexed { entry, item ->
      if (item.segment != null || item.precision != null)
        throw UnsupportedFrontendElementException("Unsupported element in a termination witness")
      val invariant = item.invariant ?: return@forEachIndexed
      val (heads, labels) = evaluationPoints(builder, invariant)
      if (heads.isEmpty() && labels.isEmpty()) {
        if (isEntry)
          throw UnsupportedFrontendElementException(
            "No evaluation point for the witness invariant at ${invariant.location}"
          )
        return@forEachIndexed
      }
      val check = parse(entry, invariant, builder)
      heads
        .flatMap { it.outgoingEdges }
        .forEach { atStart.getOrPut(it) { mutableListOf() } += check }
      for ((edge, index) in labels) {
        if (index == 0) atStart.getOrPut(edge) { mutableListOf() } += check
        else inside.getOrPut(edge) { sortedMapOf() }.getOrPut(index) { mutableListOf() } += check
      }
    }

    // Edges of one source with the same checks share the check location after the source
    val startLocs = HashMap<XcfaEdge, XcfaLocation>()
    atStart.entries.groupBy({ it.key.source to it.value.toList() }, { it.key }).forEach {
      (key, edges) ->
      val loc = checkLocation(key.second)
      builder.addEdge(XcfaEdge(key.first, loc, SequenceLabel(listOf(NopLabel)), EmptyMetaData))
      edges.forEach { startLocs[it] = loc }
    }
    for (edge in (startLocs.keys + inside.keys).distinct()) {
      builder.removeEdge(edge)
      val labels = edge.getFlatLabels()
      var source = startLocs[edge] ?: edge.source
      var from = 0
      for ((index, checks) in inside[edge].orEmpty()) {
        val loc = checkLocation(checks)
        builder.addEdge(
          XcfaEdge(source, loc, SequenceLabel(labels.subList(from, index)), edge.metadata)
        )
        source = loc
        from = index
      }
      builder.addEdge(
        XcfaEdge(
          source,
          edge.target,
          SequenceLabel(labels.subList(from, labels.size)),
          edge.metadata,
        )
      )
    }
    return builder
  }

  private fun checkLocation(checks: List<InvariantCheck>) =
    XcfaLocation(
      "__witness_check_" + XcfaLocation.uniqueCounter(),
      metadata = InvariantCheckMetaData(checks),
    )

  /**
   * The loop heads and the (edge, label index) pairs before which [invariant] is evaluated: the
   * label that starts the statement at its location, as the witness writer places them.
   */
  private fun evaluationPoints(
    builder: XcfaProcedureBuilder,
    invariant: Invariant,
  ): Pair<List<XcfaLocation>, List<Pair<XcfaEdge, Int>>> {
    val line = invariant.location.line
    fun CMetaData.startsAt(column: Int?) =
      lineNumberStart == line && (column == null || colNumberStart?.plus(1) == column)
    return when (invariant.type) {
      InvariantType.LOOP_INVARIANT,
      InvariantType.LOOP_TRANSITION_INVARIANT -> {
        val heads =
          builder.getLocs().filter { loc ->
            (loc.metadata as? CMetaData)?.loopHead?.loop?.let {
              it.lineNumberStart == line &&
                (invariant.location.column?.let { column -> it.colNumberStart + 1 == column }
                  ?: true)
            } ?: false
          }
        if (heads.any { (it.metadata as CMetaData).loopHead?.complete != true })
          throw UnsupportedFrontendElementException(
            "The loop head of the witness invariant at ${invariant.location} was lost"
          )
        heads to listOf()
      }
      InvariantType.LOCATION_INVARIANT,
      InvariantType.LOCATION_TRANSITION_INVARIANT -> {
        val starts =
          builder.getEdges().flatMap { edge ->
            edge.getFlatLabels().mapIndexedNotNull { index, label ->
              (label.metadata as? CMetaData)
                ?.takeIf { !it.notStatementStart }
                ?.let { Triple(edge, index, it) }
            }
          }
        // without a column, the leftmost statement on the line
        val column =
          invariant.location.column
            ?: starts
              .filter { it.third.startsAt(null) }
              .mapNotNull { it.third.colNumberStart?.plus(1) }
              .minOrNull()
        listOf<XcfaLocation>() to
          starts.filter { it.third.startsAt(column) }.map { it.first to it.second }
      }
    }
  }

  private fun parse(
    entry: Int,
    invariant: Invariant,
    builder: XcfaProcedureBuilder,
  ): InvariantCheck {
    if (invariant.format != Format.C_EXPRESSION && invariant.format != Format.EXT_C_EXPRESSION)
      throw UnsupportedFrontendElementException("Unsupported invariant format ${invariant.format}")
    val isTransition =
      invariant.type == InvariantType.LOOP_TRANSITION_INVARIANT ||
        invariant.type == InvariantType.LOCATION_TRANSITION_INVARIANT
    val prevNames = ANY_PREV.findAll(invariant.value).map { it.groupValues[1] }.toSet()
    val text = ANY_PREV.replace(invariant.value) { PREV_PREFIX + it.groupValues[1] }
    if ('\\' in text || (prevNames.isNotEmpty() && !isTransition))
      throw UnsupportedFrontendElementException("Unsupported witness invariant ${invariant.value}")

    val vars = builder.getVars() + builder.parent.getVars().map { it.wrappedVar }
    val byName = vars.groupBy(::cName)
    // A name declared several times cannot be resolved by its position alone
    val ambiguous = IDENTIFIER.findAll(text).map { it.value }.filter { (byName[it]?.size ?: 0) > 1 }
    if (ambiguous.any())
      throw UnsupportedFrontendElementException(
        "Ambiguous names ${ambiguous.toSet()} in the witness invariant at ${invariant.location}"
      )
    val anyPrev: Map<VarDecl<*>, VarDecl<*>> =
      prevNames.associate { name ->
        val decl =
          byName[name]?.single()
            ?: throw UnsupportedFrontendElementException("Unknown variable $name in a witness")
        val prev: VarDecl<*> = Var(PREV_PREFIX + name, decl.type)
        parseContext.metadata.create(
          prev.ref,
          "cType",
          CComplexType.getType(decl.ref, parseContext),
        )
        prev to decl
      }
    val expr =
      getBoolExpressionFromC(
        text,
        parseContext,
        false,
        false,
        NullLogger.getInstance(),
        vars + anyPrev.keys,
      )
    return InvariantCheck(entry, expr, anyPrev, isTransition)
  }

  private fun cName(decl: VarDecl<*>): String =
    parseContext.metadata.getMetadataValue(decl.name, "cName").orElse(decl.name) as String

  companion object {
    private const val PREV_PREFIX = "__theta_anyprev_"
    private val ANY_PREV = Regex("""\\at\(\s*([A-Za-z_]\w*)\s*,\s*AnyPrev\s*\)""")
    private val IDENTIFIER = Regex("""[A-Za-z_]\w*""")
  }
}
