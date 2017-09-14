/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

public final class BasicScope implements Scope {

	private final Optional<Scope> enclosingScope;
	private final SymbolTable symbolTable;

	public BasicScope(final Scope eclosingScope) {
		this.enclosingScope = Optional.ofNullable(eclosingScope);
		symbolTable = new SymbolTable();
	}

	////

	public void declare(final Symbol symbol) {
		symbolTable.add(symbol);
	}

	public void declareAll(final Collection<? extends Symbol> symbols) {
		symbolTable.addAll(symbols);
	}

	////

	@Override
	public Optional<Scope> enclosingScope() {
		return enclosingScope;
	}

	@Override
	public Optional<? extends Symbol> resolve(final String name) {
		checkNotNull(name);
		final Optional<Symbol> symbol = symbolTable.get(name);
		if (symbol.isPresent() || !enclosingScope.isPresent()) {
			return symbol;
		} else {
			return enclosingScope.get().resolve(name);
		}
	}

}
