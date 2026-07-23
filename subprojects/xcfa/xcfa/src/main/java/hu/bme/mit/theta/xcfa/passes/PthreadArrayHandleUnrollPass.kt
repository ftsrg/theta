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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Unrolls the thread create/join loops so an array of pthread handles becomes constant-indexed.
 *
 * A pthread handle is an identity key the analysis maps to a thread id ([CLibraryFunctionsPass]); an
 * array of them, `pthread_t t[N]; for (i) pthread_create(&t[i], …)`, needs one distinct key per
 * element, so the index has to be a compile-time constant when [CLibraryFunctionsPass] runs. That
 * pass runs before [ReferenceElimination] (which would rewrite `&t[i]` into the base/offset memory
 * model, losing the handle) and hence before the ordinary [LoopUnrollPass], so the create/join loops
 * are still rolled and `&t[i]` carries the loop variable as its offset.
 *
 * This pass fills the gap: on a procedure that actually creates or joins threads through an array
 * element -- and only such a procedure, so nothing else is touched -- it runs [LoopUnrollPass] early,
 * turning `&t[i]` into `&t[0]`, `&t[1]`, … before the handles are read. It sits right before
 * [CLibraryFunctionsPass] in [CPasses]; the later [LoopUnrollPass] then finds these loops already
 * unrolled and leaves them.
 */
class PthreadArrayHandleUnrollPass(private val parseContext: ParseContext) : ProcedurePass {

  private val threadFunctions = setOf("pthread_create", "pthread_join")

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder =
    if (createsThreadThroughArrayElement(builder))
      LoopUnrollPass(substituteLoopVar = true, parseContext = parseContext).run(builder)
    else builder

  private fun createsThreadThroughArrayElement(builder: XcfaProcedureBuilder): Boolean =
    builder.getEdges().any { edge ->
      edge.label.getFlatLabels().any { label ->
        label is InvokeLabel && label.name in threadFunctions && label.hasArrayElementHandle()
      }
    }

  /** The thread handle -- `params[1]` for both create and join -- is a non-constant array element. */
  private fun InvokeLabel.hasArrayElementHandle(): Boolean {
    if (params.size <= 1) return false
    var handle = params[1]
    while (handle is Reference<*, *>) handle = handle.expr
    if (handle !is Dereference<*, *, *>) return false
    val offset = handle.offset
    // A literal index (`&t[0]`, or already unrolled) needs no unrolling; only a loop-variable index
    // (`&t[i]`) does.
    return offset !is IntLitExpr && offset !is BvLitExpr
  }
}
