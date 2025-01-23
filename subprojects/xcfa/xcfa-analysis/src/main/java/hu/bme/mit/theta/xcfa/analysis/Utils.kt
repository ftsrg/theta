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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.passes.changeVars
import kotlin.reflect.KProperty

fun <K, V> Map<K, V>.reverseMapping() = this.entries.associate { it.value to it.key }

fun Valuation.changeVars(varLut: Map<out Decl<*>, VarDecl<*>>): Valuation {
  val builder = ImmutableValuation.builder()
  for (decl in this.decls) {
    if (decl in varLut) {
      builder.put(decl.changeVars(varLut), this.eval(decl).get())
    }
  }
  return builder.build()
}

internal fun <S : ExprState> XcfaState<S>.withGeneralizedVars(): S {
  val varLookup =
    processes
      .mapNotNull { (_, process) -> process.varLookup.peek()?.reverseMapping() }
      .reduceOrNull(Map<VarDecl<*>, VarDecl<*>>::plus) ?: mapOf()
  return if (sGlobal.isBottom) sGlobal else sGlobal.getState(varLookup)
}

private fun <S : ExprState> S.getState(varLookup: Map<VarDecl<*>, VarDecl<*>>): S =
  when (this) {
    is ExplState -> ExplState.of(getVal().changeVars(varLookup))
    is PredState -> PredState.of(preds.map { p -> p.changeVars(varLookup) })
    is PtrState<*> -> PtrState(innerState.getState(varLookup))
    else ->
      throw NotImplementedError(
        "Generalizing variable instances is not implemented for data states that are not explicit or predicate."
      )
  }
    as S

class LazyDelegate<T, P : Any>(val getProperty: T.() -> P) {

  private var calculated = false
  private lateinit var property: P

  operator fun getValue(thisRef: T, property: KProperty<*>): P {
    return if (calculated) this.property
    else
      thisRef.getProperty().also {
        this.property = it
        this.calculated = true
      }
  }
}

val XCFA.isInlined: Boolean by LazyDelegate {
  !this.procedures.any { p ->
    p.edges.any { e ->
      e.getFlatLabels().any { l -> l is InvokeLabel && this.procedures.any { it.name == l.name } }
    }
  }
}

fun XcfaProcessState.foldVarLookup(): Map<VarDecl<*>, VarDecl<*>> =
  this.varLookup.reduceRightOrNull { lookup, acc -> acc + lookup }
    ?: emptyMap() // right map overrides left's keys
