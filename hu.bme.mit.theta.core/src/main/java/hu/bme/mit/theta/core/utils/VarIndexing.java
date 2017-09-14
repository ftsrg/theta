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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.lang.Math.max;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;

import hu.bme.mit.theta.core.decl.VarDecl;

/**
 * Represents an immutable mapping, where each variable is associated with an
 * index. The inner builder class can also be used to create a new instance.
 */
public class VarIndexing {

	private static final VarIndexing ALL_ZERO = new Builder(0).build();
	private static final VarIndexing ALL_ONE = new Builder(1).build();

	private final int defaultIndex;
	private final Map<VarDecl<?>, Integer> varToOffset;

	private VarIndexing(final Builder builder) {
		defaultIndex = builder.defaultIndex;
		varToOffset = ImmutableMap.copyOf(builder.varToOffset);
	}

	/**
	 * Create a new instance with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New instance
	 */
	public static VarIndexing all(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		switch (defaultIndex) {
		case 0:
			return ALL_ZERO;
		case 1:
			return ALL_ONE;
		default:
			return new Builder(defaultIndex).build();
		}
	}

	/**
	 * Create a builder with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New builder
	 */
	public static Builder builder(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new Builder(defaultIndex);
	}

	/**
	 * Create a new builder from the current instance.
	 *
	 * @return New builder
	 */
	public Builder transform() {
		return new Builder(this);
	}

	/**
	 * Increment the index of a given variable with a given amount
	 *
	 * @param varDecl Variable to increment
	 * @param n Amount to increment
	 * @return Transformed indexing
	 */
	public VarIndexing inc(final VarDecl<?> varDecl, final int n) {
		checkNotNull(varDecl);
		return transform().inc(varDecl, n).build();
	}

	/**
	 * Increment the index of a given variable by one
	 *
	 * @param varDecl Variable to increment
	 * @return Transformed indexing
	 */
	public VarIndexing inc(final VarDecl<?> varDecl) {
		return inc(varDecl, 1);
	}

	/**
	 * Add another indexing to the current instance
	 *
	 * @param indexing Other indexing
	 * @return Sum of the two indexings
	 */
	public VarIndexing add(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().add(indexing.transform()).build();
	}

	/**
	 * Subtract another indexing from the current instance
	 *
	 * @param indexing Other indexing
	 * @return Difference of the two indexings
	 */
	public VarIndexing sub(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().sub(indexing.transform()).build();
	}

	/**
	 * Join another indexing to the current instance
	 *
	 * @param indexing Other indexing
	 * @return Joined indexing
	 */
	public VarIndexing join(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().join(indexing.transform()).build();
	}

	/**
	 * Get the index of a variable
	 * 
	 * @param varDecl Variable
	 * @return Index
	 */
	public int get(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		final Integer offset = varToOffset.getOrDefault(varDecl, 0);
		return defaultIndex + offset;
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "IndexMap(", ")");
		sj.add(Integer.toString(defaultIndex));
		for (final VarDecl<?> varDecl : varToOffset.keySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(varDecl.getName());
			sb.append(" -> ");
			sb.append(get(varDecl));
			sj.add(sb);
		}
		return sj.toString();
	}

	////

	public static final class Builder {
		private int defaultIndex;
		private Map<VarDecl<?>, Integer> varToOffset;

		private Builder(final int defaultIndex) {
			checkArgument(defaultIndex >= 0, "Negative default index");
			this.defaultIndex = defaultIndex;
			varToOffset = new HashMap<>();
		}

		private Builder(final VarIndexing indexing) {
			this.defaultIndex = indexing.defaultIndex;
			this.varToOffset = new HashMap<>(indexing.varToOffset);
		}

		public Builder inc(final VarDecl<?> varDecl, final int n) {
			checkNotNull(varDecl);

			if (n != 0) {
				final Integer offset = varToOffset.getOrDefault(varDecl, 0);
				final Integer newOffset = offset + n;
				checkArgument(defaultIndex + newOffset >= 0, "Negative index for variable");
				varToOffset.put(varDecl, newOffset);
			}

			return this;
		}

		public Builder inc(final VarDecl<?> varDecl) {
			return inc(varDecl, 1);
		}

		public Builder incAll() {
			defaultIndex = defaultIndex + 1;
			return this;
		}

		public Builder add(final Builder that) {
			checkNotNull(that);

			final int newDefaultIndex = this.defaultIndex + that.defaultIndex;
			final Map<VarDecl<?>, Integer> newVarToOffset = new HashMap<>();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final int index1 = this.get(varDecl);
				final int index2 = that.get(varDecl);
				final int newIndex = index1 + index2;
				checkArgument(newIndex >= 0, "Negative index for variable");
				final int newOffset = newIndex - newDefaultIndex;
				if (newOffset != 0) {
					newVarToOffset.put(varDecl, newOffset);
				}
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		public Builder sub(final Builder that) {
			checkNotNull(that);

			final int newDefaultIndex = this.defaultIndex - that.defaultIndex;
			checkArgument(newDefaultIndex >= 0, "Negative default index");
			final Map<VarDecl<?>, Integer> newVarToOffset = new HashMap<>();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final int index1 = this.get(varDecl);
				final int index2 = that.get(varDecl);
				final int newIndex = index1 - index2;
				checkArgument(newIndex >= 0, "Negative index for variable");
				final int newOffset = newIndex - newDefaultIndex;
				if (newOffset != 0) {
					newVarToOffset.put(varDecl, newOffset);
				}
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		public Builder join(final Builder that) {
			checkNotNull(that);

			final int newDefaultIndex = max(this.defaultIndex, that.defaultIndex);
			final Map<VarDecl<?>, Integer> newVarToOffset = new HashMap<>();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final int index1 = this.get(varDecl);
				final int index2 = that.get(varDecl);
				final int newIndex = max(index1, index2);
				final int newOffset = newIndex - newDefaultIndex;
				if (newOffset != 0) {
					newVarToOffset.put(varDecl, newOffset);
				}
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		public int get(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			final Integer offset = varToOffset.getOrDefault(varDecl, 0);
			return defaultIndex + offset;
		}

		public VarIndexing build() {
			return new VarIndexing(this);
		}

	}

}
