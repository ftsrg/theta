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
@file:UseContextualSerialization(Expr::class, VarDecl::class, LitExpr::class, MetaData::class)

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.model.serialization.BoolExprReferenceSerializer
import hu.bme.mit.theta.xcfa.model.serialization.LocationDefinitionSerializer
import hu.bme.mit.theta.xcfa.model.serialization.LocationReferenceSerializer
import hu.bme.mit.theta.xcfa.model.serialization.OptionalLocationReferenceSerializer
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getNonConcurrentEdges
import hu.bme.mit.theta.xcfa.utils.getPointsToGraph
import hu.bme.mit.theta.xcfa.utils.pointerPartitions
import java.util.*
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import kotlinx.serialization.UseContextualSerialization

class XCFA(
  val name: String,
  val globalVars: Set<XcfaGlobalVar>, // global variables
  val procedureBuilders: Set<XcfaProcedureBuilder> = emptySet(),
  val initProcedureBuilders: List<Pair<XcfaProcedureBuilder, List<Expr<*>>>> = emptyList(),
  var unsafeUnrollUsed: Boolean = false,
) {

  private var cachedHash: Int? = null

  val pointsToGraph by lazy { this.getPointsToGraph() }

  private lateinit var pointerPartitions: List<Pair<Set<VarDecl<*>>, Set<LitExpr<*>>>>

  var procedures: Set<XcfaProcedure> // procedure definitions
    private set

  var initProcedures:
    List<Pair<XcfaProcedure, List<Expr<*>>>> // procedure names and parameter assignments
    private set

  init {
    var phase = 0
    do {
      var ready = true
      procedureBuilders.toSet().forEach { ready = it.optimize(phase) && ready }
      initProcedureBuilders.toSet().forEach { ready = it.first.optimize(phase) && ready }
      phase++
    } while (!ready)

    procedures = procedureBuilders.toSet().map { it.build(this) }.toSet()
    initProcedures = initProcedureBuilders.toSet().map { Pair(it.first.build(this), it.second) }
    unsafeUnrollUsed =
      (procedureBuilders + initProcedureBuilders.map { it.first }).any { it.unsafeUnrollUsed }
  }

  /** Recreate an existing XCFA by substituting the procedures and initProcedures fields. */
  fun recreate(
    procedures: Set<XcfaProcedure>,
    initProcedures: List<Pair<XcfaProcedure, List<Expr<*>>>>,
  ): XCFA {
    this.procedures = procedures
    this.initProcedures = initProcedures
    return this
  }

  /**
   * Returns the pointer partitions of the XCFA. If initEdges is provided, it will be used to
   * compute the partitions, otherwise the non-concurrent edges are calculated and used.
   *
   * See [pointerPartitions][hu.bme.mit.theta.xcfa.utils.pointerPartitions].
   */
  fun getPointerPartitions(
    initEdges: Set<XcfaEdge>? = null
  ): List<Pair<Set<VarDecl<*>>, Set<LitExpr<*>>>> {
    if (!this::pointerPartitions.isInitialized) {
      val init =
        when {
          initEdges != null -> initEdges
          initProcedures.any { p ->
            p.first.edges.any { e -> e.getAllLabels().any { it is StartLabel } }
          } -> getNonConcurrentEdges(procedureBuilders.first().parent, true).first
          else -> setOf()
        }
      pointerPartitions = pointerPartitions(this, init)
    }
    return pointerPartitions
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (javaClass != other?.javaClass) return false

    other as XCFA

    if (name != other.name) return false
    if (globalVars != other.globalVars) return false
    if (procedures != other.procedures) return false
    if (initProcedures != other.initProcedures) return false

    return true
  }

  override fun hashCode(): Int {
    if (cachedHash != null) return cachedHash as Int
    var result = name.hashCode()
    result = 31 * result + globalVars.hashCode()
    result = 31 * result + procedures.hashCode()
    result = 31 * result + initProcedures.hashCode()
    cachedHash = result
    return result
  }

  override fun toString(): String {
    return "XCFA(name='$name', vars=$globalVars, procedures=$procedures, initProcedures=$initProcedures)"
  }
}

@Serializable
data class XcfaProcedure(
  val name: String,
  val params: List<Pair<VarDecl<*>, ParamDirection>>, // procedure params
  val vars: Set<VarDecl<*>>, // local variables
  val locs:
    Set<@Serializable(with = LocationDefinitionSerializer::class) XcfaLocation>, // locations
  val edges: Set<XcfaEdge>, // edges
  @Serializable(with = LocationReferenceSerializer::class)
  val initLoc: XcfaLocation, // initial location
  @Serializable(with = OptionalLocationReferenceSerializer::class)
  val finalLoc: Optional<XcfaLocation>, // final location (optional)
  @Serializable(with = OptionalLocationReferenceSerializer::class)
  val errorLoc: Optional<XcfaLocation>, // error location (optional)
  @Serializable(with = BoolExprReferenceSerializer::class) val prop: Expr<BoolType> = True(),
) {

  @Transient internal lateinit var parent: XCFA
}

@Serializable
data class XcfaLocation
@JvmOverloads
constructor(
  val name: String, // label of the location
  val initial: Boolean = false, // is this the initial location?
  val final: Boolean = false, // is this the final location?
  val error: Boolean = false, // is this the error location?
  val metadata: MetaData,
) {

  @Transient
  val incomingEdges: MutableSet<XcfaEdge> =
    LinkedHashSet() // all incoming edges in the current procedure
  @Transient
  val outgoingEdges: MutableSet<XcfaEdge> =
    LinkedHashSet() // all outgoing edges in the current procedure

  companion object {

    internal var cnt: Int = 0

    fun uniqueCounter(): Int = cnt++
  }

  override fun toString(): String {
    return "$name ${if (initial) "{init}" else ""}${if (final) "{final}" else ""}${if (error) "{error}" else ""}"
  }
}

@Serializable
data class XcfaEdge(
  @Serializable(with = LocationReferenceSerializer::class)
  val source: XcfaLocation, // source location
  @Serializable(with = LocationReferenceSerializer::class)
  val target: XcfaLocation, // target location
  val label: XcfaLabel = NopLabel, // edge label
  val metadata: MetaData,
) {

  fun withLabel(label: XcfaLabel): XcfaEdge = XcfaEdge(source, target, label, metadata)

  fun withTarget(target: XcfaLocation): XcfaEdge = XcfaEdge(source, target, label, metadata)

  fun withSource(source: XcfaLocation): XcfaEdge = XcfaEdge(source, target, label, metadata)

  fun withMetadata(metadata: MetaData): XcfaEdge = XcfaEdge(source, target, label, metadata)
}

@Serializable
data class XcfaGlobalVar
@JvmOverloads
constructor(
  val wrappedVar: VarDecl<*>,
  val initValue: LitExpr<*>? = null,
  val threadLocal: Boolean = false,
  /** The variable itself is `_Atomic`: `int * _Atomic p`. */
  val atomic: Boolean = false,
  /**
   * The *object this points at* is `_Atomic`: `_Atomic int *p`, or the pointer that
   * [ReferenceElimination] makes for an address-taken `_Atomic int`.
   *
   * A different question from [atomic], and the one a *memory* access has to ask. It is recorded
   * here rather than looked up when needed because the C types are keyed by object identity, so a
   * pass that rebuilds an expression loses them -- and by the time the analysis runs, an
   * address-taken object's pointer has been folded to a bare literal (its id) with nothing left to
   * read.
   */
  val pointsToAtomic: Boolean = false,
)

enum class ParamDirection {
  IN,
  OUT,
  INOUT,
}
