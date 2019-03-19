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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.LinkedHashMap;
import java.util.Optional;
import java.util.StringJoiner;

public final class SymbolTable {

	private final LinkedHashMap<String, Symbol> stringToSymbol;

	public SymbolTable() {
		stringToSymbol = new LinkedHashMap<>();
	}

	////

	public void add(final Symbol symbol) {
		checkNotNull(symbol);
		checkArgument(!stringToSymbol.containsKey(symbol.getName()));
		stringToSymbol.put(symbol.getName(), symbol);
	}

	public void addAll(final Iterable<? extends Symbol> symbols) {
		checkNotNull(symbols);
		for (final Symbol symbol : symbols) {
			add(symbol);
		}
	}

	public Optional<Symbol> get(final String name) {
		final Symbol symbol = stringToSymbol.get(name);
		return Optional.ofNullable(symbol);
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "SymbolTable(", ")");
		for (final Symbol symbol : stringToSymbol.values()) {
			sj.add(symbol.toString());
		}
		return sj.toString();
	}

}
