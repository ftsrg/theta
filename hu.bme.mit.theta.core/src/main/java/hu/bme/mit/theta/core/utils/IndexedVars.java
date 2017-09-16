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
package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringJoiner;
import java.util.stream.Collectors;

import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;

/**
 * Represents an immutable mapping, where each integer index can be associated
 * with a set of variables. Use the inner builder class to create a new
 * instance.
 */
public final class IndexedVars {

	private final Map<Integer, Set<VarDecl<?>>> varSets;

	private IndexedVars(final Map<Integer, Set<VarDecl<?>>> varSets) {
		this.varSets = varSets;
	}

	/**
	 * Get variables for a given index. If the index is not present, an empty
	 * set is returned.
	 *
	 * @param index Index
	 * @return Set of variables
	 */
	public Set<VarDecl<?>> getVars(final int index) {
		Set<VarDecl<?>> vars = varSets.get(index);
		if (vars == null) {
			vars = Collections.emptySet();
		}
		return Collections.unmodifiableSet(vars);
	}

	/**
	 * Get the non-empty indexes.
	 *
	 * @return Set of indexes
	 */
	public Set<Integer> getNonEmptyIndexes() {
		return varSets.keySet();
	}

	/**
	 * Check if the mapping is empty.
	 *
	 * @return True, if the mapping is empty
	 */
	public boolean isEmpty() {
		return varSets.isEmpty();
	}

	/**
	 * Get all variables that appear for any index.
	 *
	 * @return Set of variables
	 */
	public Set<VarDecl<?>> getAllVars() {
		final Set<VarDecl<?>> allVars = varSets.values().stream().flatMap(s -> s.stream()).collect(Collectors.toSet());
		return Collections.unmodifiableSet(allVars);
	}

	/**
	 * Create a new builder instance.
	 */
	public static Builder builder() {
		return new Builder();
	}

	/**
	 * Helper class for building a new instance.
	 */
	public static final class Builder {

		private final Map<Integer, Set<VarDecl<?>>> varSets;
		private boolean built;

		private Builder() {
			varSets = new HashMap<>();
			built = false;
		}

		public void add(final int i, final VarDecl<?> varDecl) {
			checkState(!built, "Already built.");
			if (!varSets.containsKey(i)) {
				varSets.put(i, new HashSet<>());
			}
			varSets.get(i).add(varDecl);
		}

		public void add(final int i, final Collection<? extends VarDecl<?>> varDecls) {
			checkState(!built, "Already built.");
			if (varDecls.isEmpty()) {
				return;
			}

			if (!varSets.containsKey(i)) {
				varSets.put(i, new HashSet<>());
			}
			varSets.get(i).addAll(varDecls);
		}

		public void add(final IndexedConstDecl<?> indexedConstDecl) {
			checkState(!built, "Already built.");
			add(indexedConstDecl.getIndex(), indexedConstDecl.getVarDecl());
		}

		public IndexedVars build() {
			checkState(!built, "Already built.");
			built = true;
			return new IndexedVars(varSets);
		}
	}

	@Override
	public String toString() {
		final ToStringBuilder builder = Utils.toStringBuilder(getClass().getSimpleName());

		for (final Entry<Integer, Set<VarDecl<?>>> entry : varSets.entrySet()) {
			final StringJoiner sj = new StringJoiner(", ", entry.getKey() + ": ", "");
			entry.getValue().forEach(v -> sj.add(v.getName()));
			builder.add(sj.toString());
		}
		return builder.toString();
	}
}
