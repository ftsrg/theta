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
package hu.bme.mit.theta.xcfa.passes.concurrency

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.library.CLibraryFunctionsPass
import hu.bme.mit.theta.xcfa.passes.library.CLibraryFunctionsPass.Companion.THREAD_DONE
import hu.bme.mit.theta.xcfa.passes.library.CLibraryFunctionsPass.Companion.THREAD_NEXT_RESULT_ID
import hu.bme.mit.theta.xcfa.passes.library.CLibraryFunctionsPass.Companion.THREAD_RESULTS
import hu.bme.mit.theta.xcfa.passes.library.CLibraryFunctionsPass.Companion.THREAD_RESULT_ID_PREFIX
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.getAtomicBlockInnerLocations
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Makes started threads store their result for `pthread_join`. [CLibraryFunctionsPass] passes such
 * a thread its result id as an extra start argument; this pass starts a copy of the routine instead
 * that takes the id as a parameter and, on reaching its final location, atomically writes its
 * return value into [THREAD_RESULTS] and sets its [THREAD_DONE] flag under that id (whichever of
 * the two the model has).
 *
 * It runs after inlining, so that the copy is of the routine's finished body, and in its own phase.
 */
class ThreadResultPass : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val global = { name: String ->
      builder.parent.getVars().firstOrNull { it.wrappedVar.name == name }?.wrappedVar
    }
    val results = global(THREAD_RESULTS)
    val done = global(THREAD_DONE)
    if (results == null && done == null) return builder
    for (edge in builder.getEdges().toList()) {
      val labels = edge.getFlatLabels()
      if (labels.none { it.resultId() != null && !it.storesResult() }) continue
      val updated =
        labels.map { label ->
          if (label !is StartLabel || label.resultId() == null || label.storesResult()) label
          else label.copy(name = storingCopy(builder, label, results, done).name)
        }
      builder.removeEdge(edge)
      builder.addEdge(edge.withLabel(SequenceLabel(updated, edge.label.metadata)))
    }
    if (builder.parent.getInitProcedures().any { it.first === builder }) initialize(builder)
    return builder
  }

  /**
   * Assigns the result globals their initial values on entry: some backends (e.g. OC) take a
   * global's value only from assignments, not from its `initValue`.
   */
  private fun initialize(entry: XcfaProcedureBuilder) {
    check(
      entry.parent.getProcedures().none { proc ->
        proc.getEdges().any { e ->
          e.getFlatLabels().any {
            (it is InvokeLabel && it.name == entry.name) ||
              (it is StartLabel && it.name == entry.name)
          }
        }
      }
    ) {
      "Unsupported thread results: entry point ${entry.name} is also called or started"
    }
    val initializers =
      entry.parent
        .getVars()
        .filter {
          val name = it.wrappedVar.name
          name == THREAD_RESULTS ||
            name == THREAD_NEXT_RESULT_ID ||
            name.startsWith(THREAD_RESULT_ID_PREFIX)
        }
        .map { AssignStmtLabel(it.wrappedVar, checkNotNull(it.initValue)) }
    // On the entry edges themselves: later passes place the initializations of the ghost state and
    // of address-taken objects there, which would otherwise end up after the code using them.
    entry.initLoc.outgoingEdges.toList().forEach {
      entry.removeEdge(it)
      entry.addEdge(
        it.withLabel(SequenceLabel(initializers + it.getFlatLabels(), it.label.metadata))
      )
    }
  }

  private fun XcfaLabel.resultId(): VarDecl<*>? =
    ((this as? StartLabel)?.params?.lastOrNull() as? RefExpr<*>)?.decl?.takeIf {
      it.name.startsWith(THREAD_RESULT_ID_PREFIX)
    } as VarDecl<*>?

  private fun XcfaLabel.storesResult() = (this as StartLabel).name.endsWith(SUFFIX)

  private fun storingCopy(
    builder: XcfaProcedureBuilder,
    label: StartLabel,
    results: VarDecl<*>?,
    done: VarDecl<*>?,
  ): XcfaProcedureBuilder {
    val name = label.name + SUFFIX
    builder.parent
      .getProcedures()
      .firstOrNull { it.name == name }
      ?.let {
        return it
      }
    val routine = builder.parent.getProcedures().single { it.name == label.name }
    check(routine.getParams().size + 1 == label.params.size) {
      "Unexpected start of ${routine.name} with ${label.params.size} arguments"
    }
    val ret = routine.getParams().firstOrNull { it.second == ParamDirection.OUT }?.first
    if (results != null) {
      val resultType = (results.type as ArrayType<*, *>).elemType
      check(ret != null && ret.type == resultType) {
        "Unsupported thread result: ${routine.name} does not return a value of type $resultType"
      }
    }

    val copy = routine.deepCopy("thread_result").also { it.name = name }
    val id = Var("__theta_thread_result_id", label.resultId()!!.type)
    copy.addParam(id, ParamDirection.IN)
    copy.finalLoc.ifPresent { final ->
      val atomic = final in getAtomicBlockInnerLocations(copy)
      val store = XcfaLocation("${final.name}_store_result", metadata = final.metadata)
      copy.addLoc(store)
      final.incomingEdges.toList().forEach {
        copy.removeEdge(it)
        copy.addEdge(it.withTarget(store))
      }
      val writes =
        listOfNotNull(
          results?.let { AssignStmtLabel(it, write(it, id.ref, ret!!.ref)) },
          done?.let { AssignStmtLabel(it, write(it, id.ref, True())) },
        )
      val labels = if (atomic) writes else listOf(AtomicBeginLabel()) + writes + AtomicEndLabel()
      copy.addEdge(XcfaEdge(store, final, SequenceLabel(labels), final.metadata))
    }
    builder.parent.addProcedure(copy)
    // The copy may itself start threads whose result is joined.
    run(copy)
    copy.completeOptimizationPhaseOf(builder)
    return copy
  }

  @Suppress("UNCHECKED_CAST")
  private fun write(array: VarDecl<*>, index: Expr<*>, value: Expr<*>): Expr<*> =
    Write((array as VarDecl<ArrayType<Type, Type>>).ref, index as Expr<Type>, value as Expr<Type>)

  companion object {
    private const val SUFFIX = "__theta_thread_result"
  }
}
