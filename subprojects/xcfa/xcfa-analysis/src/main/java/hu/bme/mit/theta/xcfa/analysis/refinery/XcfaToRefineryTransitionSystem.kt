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
package hu.bme.mit.theta.xcfa.analysis.refinery

import hu.bme.mit.theta.analysis.algorithm.refinery.ActionLiteralProvider
import hu.bme.mit.theta.analysis.algorithm.refinery.MemoryAllocationExpr
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryRule
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.refinerified
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import tools.refinery.logic.term.Variable
import tools.refinery.logic.term.truthvalue.TruthValue
import tools.refinery.store.dse.transition.actions.ActionLiterals

class XcfaRefineryTransitionSystemBuilder(
  xcfa: XCFA,
  parseContext: ParseContext,
  property: ErrorDetection,
) : RefineryTransitionSystemBuilder() {

  companion object {
    internal const val LOCATION_ENUM = "Location"
    internal const val LOCATION_DECLARATION = "loc"
  }

  init {
    check(xcfa.initProcedures.size == 1) { "XCFA must have exactly one initial procedure." }
    check(property == ErrorDetection.ERROR_LOCATION)
  }

  private val procedure = xcfa.initProcedures.first().first

  private val pointers =
    procedure.vars
      .filter {
        val cType = parseContext.metadata.getMetadataValue(it.ref, "cType")
        cType.isPresent && cType.get() is CPointer
      }
      .toSet()

  private val locations: MutableSet<String> = mutableSetOf()

  private val locationDeclaration: String
    get() =
      """
      |enum $LOCATION_ENUM {
      |    ${locations.joinToString(", ")}
      |}
      """
        .trimMargin()

  override val environmentDeclarations: List<String> // add program counter (xcfa location)
    get() = listOf("$LOCATION_ENUM $LOCATION_DECLARATION") + super.environmentDeclarations

  override val environmentSetup: String
    get() = listOf(locationDeclaration, super.environmentSetup).joinToString("\n\n")

  override val initialStateDeclarations: List<String>
    get() =
      super.initialStateDeclarations +
        listOf(
          "$LOCATION_DECLARATION($ENVIRONMENT, ${procedure.initLoc.name.refinerified}).",
          "scope NamedPointer += 0.",
        ) +
        variables.map { "${it.name.refinerified}($ENVIRONMENT): 0." } +
        pointers.flatMap {
          val name = it.name.refinerified
          val pointer = "pointer_$name"
          listOf(
            "atom $name.",
            "NamedPointer($name).",
            "pointer($name, $pointer).",
            "target($pointer, null).",
            "offset($pointer): 0.",
            "MemoryObject::size($pointer): 4.", // C pointer size
          )
        }

  private val xcfaTransitionBuilder =
    XcfaRefineryTransitionRuleBuilder(locations, variables, pointers)

  override val transitions: List<RefineryRule> =
    xcfa.initProcedures.first().first.edges.flatMap { edge -> xcfaTransitionBuilder.build(edge) }

  override val errorProperty: String
    get() = "$LOCATION_DECLARATION(${ENVIRONMENT}, ${procedure.errorLoc.get().name.refinerified})"
}

class XcfaRefineryTransitionRuleBuilder(
  private val locations: MutableSet<String>,
  variables: MutableSet<Decl<*>>,
  pointers: Set<Decl<*>>,
) : RefineryTransitionRuleBuilder<XcfaEdge>(variables, pointers) {

  companion object {
    private val XcfaLabel.supported: Boolean
      get() =
        this::class in
          setOf(StmtLabel::class, NopLabel::class, SequenceLabel::class, NondetLabel::class) ||
          (this is InvokeLabel && this.name in listOf("malloc"))
  }

  private val env = RefineryTransitionSystemBuilder.ENVIRONMENT
  private val loc = XcfaRefineryTransitionSystemBuilder.LOCATION_DECLARATION
  @Suppress("PrivatePropertyName")
  private val Location = XcfaRefineryTransitionSystemBuilder.LOCATION_ENUM

  override fun build(transition: XcfaEdge): Set<RefineryRule> {
    check(transition.getAllLabels().all { it.supported }) {
      "Unsupported XCFA label found in XCFA->Refinery transition: ${transition.label}"
    }
    val sourceLocName = transition.source.name.refinerified
    val targetLocName = transition.target.name.refinerified
    val name = "${sourceLocName}__to__${targetLocName}"
    val label = transition.label.replaceInvokes()
    val topRule = label.toStmt().toRules()
    topRule.setIds()
    return topRule.allRules
      .mapIndexed { index, rule ->
        val source = if (rule.preId == topRule.preId) sourceLocName else "${name}__${rule.preId}"
        val target = if (rule.postId == topRule.postId) targetLocName else "${name}__${rule.postId}"
        locations.add(source)
        locations.add(target)
        val locPrecondition = "$loc($env, $Location::$source)"
        val env = rule.actionParameters.find { it.name == env } ?: Variable.of(env)
        val targetVar = Variable.of(target)
        val locActions =
          listOf<ActionLiteralProvider>(
            { ActionLiterals.constant(env, getNodeId(this@XcfaRefineryTransitionRuleBuilder.env)) },
            { ActionLiterals.constant(targetVar, getNodeId("$Location::$target")) },
            { ActionLiterals.put(getStorageSymbol(loc), TruthValue.TRUE, env, targetVar) },
          )
        rule
          .copy(
            preConditionClauses = setOf(locPrecondition) + rule.preConditionClauses,
            actionLiterals = rule.actionLiterals + locActions,
          )
          .toRefineryRule("${name}__$index")
      }
      .toSet()
  }

  private fun XcfaLabel.replaceInvokes(): XcfaLabel =
    when (this) {
      is InvokeLabel ->
        when (name) {
          "malloc" -> {
            val ret = (params[0] as RefExpr).decl as VarDecl
            val size = (params[1] as IntLitExpr).value
            AssignStmtLabel(ret, MemoryAllocationExpr(size, ret.type), metadata)
          }
          else -> error("Unsupported invoke label: $this")
        }
      is SequenceLabel -> SequenceLabel(labels.map { it.replaceInvokes() }, metadata)
      is NondetLabel -> NondetLabel(labels.map { it.replaceInvokes() }.toSet(), metadata)
      else -> this
    }
}
