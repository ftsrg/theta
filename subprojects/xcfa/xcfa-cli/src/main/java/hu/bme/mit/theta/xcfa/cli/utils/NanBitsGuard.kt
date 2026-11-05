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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.c2xcfa.FP_BITS_PREFIX
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.fptype.FpAssignExpr
import hu.bme.mit.theta.core.type.fptype.FpExprs.IsNan
import hu.bme.mit.theta.core.type.fptype.FpFromIeeeBvExpr
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.model.NondetLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel

/**
 * Whether the counterexample [trace] needs a NaN to be written through a floating-point union
 * member. The bits of such a NaN can be any NaN pattern in the model (an over-approximation, see
 * `FrontendXcfaBuilder.ieeeBitsOf`), so the trace is checked again with these values restricted to
 * numbers. [concretize] must throw for an infeasible trace; then the Unsafe result may be spurious.
 */
fun <S : XcfaState<*>> needsNanBits(
  trace: Trace<S, XcfaAction>,
  concretize: (Trace<S, XcfaAction>) -> Any,
): Boolean {
  var found = false
  val actions =
    trace.actions.map { action ->
      val label = action.label.withoutNanBits { found = true }
      if (label === action.label) action
      else action.withLabel(label as? SequenceLabel ?: SequenceLabel(listOf(label)))
    }
  if (!found) return false
  return try {
    concretize(Trace.of(trace.states, actions))
    false
  } catch (e: Exception) {
    true
  }
}

private fun XcfaLabel.withoutNanBits(onFound: () -> Unit): XcfaLabel =
  when (this) {
    is SequenceLabel -> SequenceLabel(labels.map { it.withoutNanBits(onFound) }, metadata)
    is NondetLabel -> NondetLabel(labels.map { it.withoutNanBits(onFound) }.toSet(), metadata)
    is StmtLabel -> {
      val cond = (stmt as? AssumeStmt)?.cond
      val bits = ((cond as? FpAssignExpr)?.leftOp as? FpFromIeeeBvExpr)?.op as? RefExpr<*>
      if (cond is FpAssignExpr && bits != null && FP_BITS_PREFIX in bits.decl.name) {
        onFound()
        StmtLabel(Assume(And(cond, Not(IsNan(cond.rightOp)))), choiceType, metadata)
      } else this
    }
    else -> this
  }
