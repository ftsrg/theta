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
package hu.bme.mit.theta.xcfa.analysis.dss.analysis

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.stmt.Stmts.Havoc
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.EmptyMetaData
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.NopLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedure
import hu.bme.mit.theta.xcfa.utils.collectVars
import java.util.Optional

/**
 * [original] with every edge reversed, so DSS on [xcfa] runs from the error locations towards the
 * entry: its violation conditions are exact sets of states reachable from the entry, and its
 * postconditions over-approximate the states that can reach an error.
 *
 * `__rev_init` leads to the clone of every error location, and the clone of the original entry is
 * the error; locations that cannot reach an error are left out. Clones are renamed, as
 * [XcfaLocation] equality would otherwise conflate them with the originals.
 */
class ProgramReversal(
  val original: XcfaProcedure,
  val xcfa: XCFA,
  val procedure: XcfaProcedure,
  /** The clone of each original location that can reach an error. */
  val reversedOf: Map<XcfaLocation, XcfaLocation>,
  val originalOf: Map<XcfaLocation, XcfaLocation>,
  /** The original of each reversed edge; the synthetic edges have none. */
  val originalEdgeOf: Map<XcfaEdge, XcfaEdge>,
  /** The per-variable temporaries of reversed self-referencing assignments. */
  val temporaries: Set<VarDecl<*>>,
) {

  /** The original path of a path of [procedure], from the entry towards the error. */
  fun originalPath(reversedPath: List<XcfaEdge>): List<XcfaEdge> =
    reversedPath.mapNotNull(originalEdgeOf::get).reversed()
}

private const val REVERSED_SUFFIX = "__rev"
private const val TEMPORARY_PREFIX = "__dss_rev_"

/** Reverses the single procedure of [xcfa]; labels without an exact reversal throw. */
fun reverseProgram(xcfa: XCFA): ProgramReversal {
  val original =
    xcfa.procedures.singleOrNull()
      ?: throw UnsupportedOperationException("DSS can only reverse single-procedure programs")

  val canReachError = LinkedHashSet<XcfaLocation>()
  val pending = ArrayDeque(original.locs.filter { it.error })
  while (pending.isNotEmpty()) {
    val location = pending.removeFirst()
    if (canReachError.add(location)) location.incomingEdges.forEach { pending.addLast(it.source) }
  }

  // An entry with incoming edges gets a dead-end `__rev_err` after its clone instead
  val entryIsError = original.initLoc.incomingEdges.isEmpty()
  val reversedOf =
    original.locs
      .filter { it in canReachError }
      .associateWith {
        XcfaLocation(
          it.name + REVERSED_SUFFIX,
          error = entryIsError && it == original.initLoc,
          metadata = it.metadata,
        )
      }
  val takenNames = (xcfa.collectVars() + original.vars).map { it.name }.toMutableSet()
  val temporaries = LinkedHashMap<VarDecl<*>, VarDecl<*>>()
  val reversal = LabelReversal { variable ->
    temporaries.getOrPut(variable) {
      var name = TEMPORARY_PREFIX + variable.name
      while (!takenNames.add(name)) name += "_"
      Var(name, variable.type)
    }
  }

  val edges = LinkedHashSet<XcfaEdge>()
  val originalEdgeOf = LinkedHashMap<XcfaEdge, XcfaEdge>()
  fun connect(source: XcfaLocation, target: XcfaLocation, label: XcfaLabel, of: XcfaEdge?) {
    val edge = XcfaEdge(source, target, label, of?.metadata ?: EmptyMetaData)
    source.outgoingEdges.add(edge)
    target.incomingEdges.add(edge)
    edges.add(edge)
    if (of != null) originalEdgeOf[edge] = of
  }

  // A source of a kept edge's target reaches an error through it, so it is kept, too
  for (edge in original.edges.filter { it.target in canReachError }) {
    val label = reversal.reverse(edge.label)
    connect(reversedOf.getValue(edge.target), reversedOf.getValue(edge.source), label, edge)
  }
  // A hub keeps the entry's single outgoing edge, which the decompositions rely on
  val init = XcfaLocation("__rev_init", initial = true, metadata = EmptyMetaData)
  val hub = XcfaLocation("__rev_hub", metadata = EmptyMetaData)
  connect(init, hub, NopLabel, null)
  original.locs
    .filter { it.error }
    .forEach { connect(hub, reversedOf.getValue(it), NopLabel, null) }
  val error =
    reversedOf[original.initLoc]?.let { entry ->
      if (entry.error) entry
      else
        XcfaLocation("__rev_err", error = true, metadata = EmptyMetaData).also {
          connect(entry, it, NopLabel, null)
        }
    }

  val procedure =
    XcfaProcedure(
      name = original.name + REVERSED_SUFFIX,
      params = emptyList(),
      vars = original.vars + temporaries.values,
      locs = linkedSetOf(init, hub) + reversedOf.values + listOfNotNull(error),
      edges = edges,
      initLoc = init,
      finalLoc = Optional.empty(),
      errorLoc = Optional.ofNullable(error),
    )
  // The public constructor would re-run the pass pipeline on builders
  val reversedXcfa =
    XCFA(xcfa.name + REVERSED_SUFFIX, xcfa.globalVars)
      .recreate(setOf(procedure), listOf(procedure to emptyList()))
  return ProgramReversal(
    original,
    reversedXcfa,
    procedure,
    reversedOf,
    reversedOf.entries.associate { (location, clone) -> clone to location },
    originalEdgeOf,
    temporaries.values.toSet(),
  )
}

/**
 * The inverse relation of each label: the weakest existential precondition of a reversed label is
 * the strongest postcondition of the original, so violation conditions stay exact.
 */
private class LabelReversal(private val temporaryOf: (VarDecl<*>) -> VarDecl<*>) {

  fun reverse(label: XcfaLabel): XcfaLabel =
    when (label) {
      is NopLabel -> label
      is SequenceLabel -> SequenceLabel(label.labels.reversed().map(::reverse), label.metadata)
      is NondetLabel -> NondetLabel(label.labels.map(::reverse).toSet(), label.metadata)
      is StmtLabel ->
        when (val stmt = label.stmt) {
          is AssumeStmt,
          is HavocStmt<*>,
          is SkipStmt -> label
          is AssignStmt<*> -> reverse(stmt, label)
          else -> unsupported(label)
        }
      else -> unsupported(label)
    }

  /** `x := e` is `assume x == e; havoc x`; with `x` in `e`, its old value is a temporary `t`. */
  private fun reverse(stmt: AssignStmt<*>, label: StmtLabel): XcfaLabel {
    val variable = stmt.varDecl
    val value = stmt.expr
    fun step(stmt: hu.bme.mit.theta.core.stmt.Stmt) = StmtLabel(stmt, metadata = label.metadata)
    if (variable !in ExprUtils.getVars(value)) {
      return SequenceLabel(
        listOf(step(Assume(exactEq(variable.ref, value))), step(Havoc(variable))),
        label.metadata,
      )
    }
    val temporary = temporaryOf(variable)
    val old = BasicSubstitution.builder().put(variable, temporary.ref).build().apply(value)
    return SequenceLabel(
      listOf(
        step(Havoc(temporary)),
        step(Assume(exactEq(variable.ref, old))),
        step(assign(variable, temporary)),
        step(Havoc(temporary)),
      ),
      label.metadata,
    )
  }

  /** Equality of values: IEEE `fp.eq` would drop NaN and conflate the zeros. */
  @Suppress("UNCHECKED_CAST")
  private fun exactEq(left: Expr<*>, right: Expr<*>): Expr<BoolType> =
    when (left.type) {
      is FpType -> FpAssign(left as Expr<FpType>, right as Expr<FpType>)
      is IntType,
      is RatType,
      is BvType,
      is BoolType,
      is ArrayType<*, *>,
      is EnumType -> AbstractExprs.Eq(left, right)
      else ->
        throw UnsupportedOperationException("DSS cannot reverse an assignment of type ${left.type}")
    }

  @Suppress("UNCHECKED_CAST")
  private fun <T : Type> assign(variable: VarDecl<T>, value: VarDecl<*>) =
    Assign(variable, value.ref as Expr<T>)

  private fun unsupported(label: XcfaLabel): Nothing =
    throw UnsupportedOperationException("DSS cannot reverse $label (${label.javaClass.simpleName})")
}
