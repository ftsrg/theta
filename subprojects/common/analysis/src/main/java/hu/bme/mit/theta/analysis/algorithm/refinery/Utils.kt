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

package hu.bme.mit.theta.analysis.algorithm.refinery

import tools.refinery.language.semantics.ProblemTrace
import tools.refinery.logic.dnf.FunctionalQuery
import tools.refinery.logic.dnf.Query
import tools.refinery.logic.term.NodeVariable
import tools.refinery.logic.term.Variable
import tools.refinery.store.dse.transition.actions.ActionLiteral
import tools.refinery.store.model.ModelStoreBuilder
import tools.refinery.store.reasoning.ReasoningBuilder
import tools.refinery.store.representation.Symbol

@Suppress("JavaDefaultMethodsNotOverriddenByDelegation")
class ProblemContext(private val problemTrace: ProblemTrace, storeBuilder: ModelStoreBuilder) : ProblemTrace by problemTrace {

  private val reasoningBuilder = storeBuilder.getAdapter(ReasoningBuilder::class.java)

  @Suppress("UNCHECKED_CAST")
  fun <T> getStorageSymbol(name: String): Symbol<T> {
    val partialSymbol = getPartialSymbol(name)
    return reasoningBuilder.getStorageSymbolForPartialSymbol(partialSymbol) as? Symbol<T>
      ?: error("No storage symbol found for $name")
  }

  inline fun <reified S, reified T : S> List<ProblemContext.() -> Any?>.reduce(
    operator: (S, T) -> S
  ): S =
    fold(cast<S>(first())) { acc, value ->
      val v: T = cast(value)
      operator(acc, v)
    }

  inline fun <reified R> cast(expr: ProblemContext.() -> Any?): R = expr() as R

  fun <T> getHelperQuery(
    name: String,
    type: Class<T>,
    parameters: List<NodeVariable> = listOf(),
  ): FunctionalQuery<T> {
    val valueTerm = getPartialFunction(name).call(*parameters.toTypedArray()).asType(type)
    val output = Variable.of("output", type)
    return Query.builder().output(output).clause(output.assign(valueTerm)).build()
  }
}

typealias ActionLiteralProvider = ProblemContext.() -> ActionLiteral

class NameProvider(private val provider: (String) -> String) {
  lateinit var name: String

  operator fun invoke(): String = provider(name)
}

class RefineryExprResult<T>(val expr: String, val domainExpr: T? = null) {

  override fun toString(): String = expr
}
