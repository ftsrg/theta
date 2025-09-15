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
package hu.bme.mit.theta.xcfa

import hu.bme.mit.theta.common.dsl.MutableScope
import hu.bme.mit.theta.common.dsl.Scope
import hu.bme.mit.theta.common.dsl.Symbol
import hu.bme.mit.theta.common.dsl.SymbolTable
import java.util.*

class XcfaScope(
  private val symbolTable: SymbolTable = SymbolTable(),
  private val enclosingScope: Scope? = null,
) : MutableScope {

  override fun enclosingScope(): Optional<out Scope> {
    return Optional.ofNullable(enclosingScope)
  }

  override fun resolve(name: String?): Optional<out Symbol> {
    val resolved = symbolTable[name]
    return if (resolved.isEmpty) enclosingScope?.resolve(name) ?: Optional.empty() else resolved
  }

  override fun add(symbol: Symbol) {
    symbolTable.add(symbol)
  }

  override fun addAll(symbols: Iterable<Symbol>) {
    symbolTable.addAll(symbols)
  }

  override fun toString(): String {
    return "Scope{\nenclosingScope: ${enclosingScope}\nsymbolTable: $symbolTable }"
  }
}
