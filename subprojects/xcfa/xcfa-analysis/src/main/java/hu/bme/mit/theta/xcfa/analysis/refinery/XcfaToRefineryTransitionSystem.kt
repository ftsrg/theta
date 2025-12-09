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

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryRule
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.getAllLabels

class XcfaRefineryTransitionSystemBuilder(private val xcfa: XCFA, parseContext: ParseContext) :
  RefineryTransitionSystemBuilder() {

  companion object {
    internal const val LOCATION_DECLARATION_NAME = "loc"
  }

  init {
    check(xcfa.initProcedures.size == 1) { "XCFA must have exactly one initial procedure." }
  }

  private val pointers =
    xcfa.initProcedures
      .first()
      .first
      .vars
      .filter {
        val cType = parseContext.metadata.getMetadataValue(it.ref, "cType")
        cType.isPresent && cType.get() is CPointer
      }
      .toSet()

  private val xcfaTransitionBuilder = XcfaRefineryTransitionRuleBuilder(variables, pointers)

  override val environmentDeclarations: List<String> // add program counter (xcfa location)
    get() = listOf("string $LOCATION_DECLARATION_NAME") + super.environmentDeclarations

  override val transitionDeclarations: List<String>
    get() =
      xcfa.initProcedures.first().first.edges.flatMap { edge ->
        xcfaTransitionBuilder.build(edge).map { it.toString() }
      }
}

class XcfaRefineryTransitionRuleBuilder(variables: MutableSet<Decl<*>>, pointers: Set<Decl<*>>) :
  RefineryTransitionRuleBuilder<XcfaEdge>(variables, pointers) {

  companion object {
    private val supportedXcfaLabels =
      setOf(StmtLabel::class, NopLabel::class, SequenceLabel::class, NondetLabel::class)
  }

  private val env = RefineryTransitionSystemBuilder.ENVIRONMENT
  private val loc = XcfaRefineryTransitionSystemBuilder.LOCATION_DECLARATION_NAME

  override fun build(transition: XcfaEdge): Set<RefineryRule> {
    check(transition.getAllLabels().all { it::class in supportedXcfaLabels }) {
      "Unsupported XCFA label found in XCFA->Refinery transition."
    }
    val name = "${transition.source.name}__to__${transition.target.name}"
    val topRule = transition.label.toStmt().toRules()
    topRule.setIds()
    return topRule.allRules
      .mapIndexed { index, rule ->
        val sourceName =
          if (rule.preId == topRule.preId) transition.source.name else "${name}__${rule.preId}"
        val targetName =
          if (rule.postId == topRule.postId) transition.target.name else "${name}__${rule.postId}"
        val locPrecondition = "$loc($env) == \"$sourceName\""
        val locAction = "$loc($env): \"$targetName\""
        rule
          .copy(
            preConditionClauses = listOf(locPrecondition) + rule.preConditionClauses,
            actionClauses = rule.actionClauses + listOf(locAction),
          )
          .toRefineryRule("${name}__$index")
      }
      .toSet()
  }
}
