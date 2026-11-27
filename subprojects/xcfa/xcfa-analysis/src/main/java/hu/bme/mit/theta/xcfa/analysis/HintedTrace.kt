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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten

/**
 * A counterexample with the values its backend found for the havocs of each action, in flat label
 * order (null where it does not know one). They are only hints for the trace concretizer.
 */
class HintedTrace<S>(
  states: List<S>,
  actions: List<XcfaAction>,
  val inputs: List<List<LitExpr<*>?>>,
) : Trace<S, XcfaAction>(states, actions) {

  init {
    require(inputs.size == actions.size) { "#inputs = #actions must hold." }
  }

  companion object {

    /** A trace whose hints are the havoc values [valuations], one per state, determine. */
    @JvmStatic
    fun <S> of(
      states: List<S>,
      actions: List<XcfaAction>,
      valuations: List<Valuation>,
    ): HintedTrace<S> =
      HintedTrace(states, actions, actions.mapIndexed { i, a -> havocValues(a, valuations[i + 1]) })
  }
}

/**
 * The values of [action]'s havocs that [post], a valuation after the action, determines: that of
 * each havoc whose variable no later label of the action writes.
 */
fun havocValues(action: XcfaAction, post: Valuation): List<LitExpr<*>?> {
  val writtenLater = mutableSetOf<VarDecl<*>>()
  val values = ArrayDeque<LitExpr<*>?>()
  for (flat in action.label.getFlatLabels().asReversed()) {
    val stmt = (flat as? StmtLabel)?.stmt
    if (stmt is HavocStmt<*>) {
      values.addFirst(
        if (stmt.varDecl in writtenLater) null else post.eval(stmt.varDecl).orElse(null)
      )
      writtenLater.add(stmt.varDecl)
    } else if (stmt != null) {
      writtenLater.addAll(StmtUtils.getWrittenVars(stmt))
    } else {
      writtenLater.addAll(flat.collectVarsWithAccessType().filter { it.value.isWritten }.keys)
    }
  }
  return values.toList()
}
