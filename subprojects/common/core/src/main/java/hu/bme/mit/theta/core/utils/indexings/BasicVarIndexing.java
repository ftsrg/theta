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
package hu.bme.mit.theta.core.utils.indexings;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.lang.Math.max;

/**
 * Represents an immutable mapping, where each variable is associated with an
 * index. The inner builder class can also be used to create a new instance.
 */
public class BasicVarIndexing implements VarIndexing {

	private static final BasicVarIndexing ALL_ZERO = new BasicVarIndexingBuilder(0).build();
	private static final BasicVarIndexing ALL_ONE = new BasicVarIndexingBuilder(1).build();

	private final int defaultIndex;
	private final Map<VarDecl<?>, Integer> varToOffset;

	private BasicVarIndexing(final BasicVarIndexingBuilder builder) {
		defaultIndex = builder.defaultIndex;
		varToOffset = ImmutableMap.copyOf(builder.varToOffset);
	}

	/**
	 * Create a new instance with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New instance
	 */
	static BasicVarIndexing all(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		switch (defaultIndex) {
			case 0:
				return ALL_ZERO;
			case 1:
				return ALL_ONE;
			default:
				return new BasicVarIndexingBuilder(defaultIndex).build();
		}
	}

	/**
	 * Create a builder with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New builder
	 */
	static BasicVarIndexingBuilder builder(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new BasicVarIndexingBuilder(defaultIndex);
	}

	/**
	 * Create a new builder from the current instance.
	 *
	 * @return New builder
	 */
	@Override
	public BasicVarIndexingBuilder transform() {
		return new BasicVarIndexingBuilder(this);
	}

	/**
	 * Increment the index of a given variable with a given amount
	 *
	 * @param varDecl Variable to increment
	 * @param n       Amount to increment
	 * @return Transformed indexing
	 */
	public BasicVarIndexing inc(final VarDecl<?> varDecl, final int n) {
		checkNotNull(varDecl);
		return transform().inc(varDecl, n).build();
	}

	/**
	 * Increment the index of a given variable by one
	 *
	 * @param varDecl Variable to increment
	 * @return Transformed indexing
	 */
	@Override
	public BasicVarIndexing inc(final VarDecl<?> varDecl) {
		return inc(varDecl, 1);
	}

	/**
	 * Add another indexing to the current instance
	 *
	 * @param indexing Other indexing
	 * @return Sum of the two indexings
	 */
	@Override
	public BasicVarIndexing add(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().add(indexing.transform()).build();
	}

	/**
	 * Subtract another indexing from the current instance
	 *
	 * @param indexing Other indexing
	 * @return Difference of the two indexings
	 */
	@Override
	public BasicVarIndexing sub(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().sub(indexing.transform()).build();
	}

	/**
	 * Join another indexing to the current instance
	 *
	 * @param indexing Other indexing
	 * @return Joined indexing
	 */
	@Override
	public BasicVarIndexing join(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().join(indexing.transform()).build();
	}

	/**
	 * Get the index of a variable
	 *
	 * @param varDecl Variable
	 * @return Index
	 */
	@Override
	public int get(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		final Integer offset = varToOffset.getOrDefault(varDecl, 0);
		return defaultIndex + offset;
	}

	public static class BasicVarIndexingBuilder implements VarIndexingBuilder {
		private int defaultIndex;
		private Map<VarDecl<?>, Integer> varToOffset;

		private BasicVarIndexingBuilder(final int defaultIndex) {
			checkArgument(defaultIndex >= 0, "Negative default index");
			this.defaultIndex = defaultIndex;
			varToOffset = Containers.createMap();
		}

		private BasicVarIndexingBuilder(final BasicVarIndexing indexing) {
			this.defaultIndex = indexing.defaultIndex;
			this.varToOffset = Containers.createMap(indexing.varToOffset);
		}

		public BasicVarIndexingBuilder inc(final VarDecl<?> varDecl, final int n) {
			checkNotNull(varDecl);

			if (n != 0) {
				final Integer offset = varToOffset.getOrDefault(varDecl, 0);
				final Integer newOffset = offset + n;
				checkArgument(defaultIndex + newOffset >= 0, "Negative index for variable");
				varToOffset.put(varDecl, newOffset);
			}

			return this;
		}

		@Override
		public BasicVarIndexingBuilder inc(final VarDecl<?> varDecl) {
			return inc(varDecl, 1);
		}

		@Override
		public BasicVarIndexingBuilder incAll() {
			defaultIndex = defaultIndex + 1;
			return this;
		}

		@Override
		public BasicVarIndexingBuilder add(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof BasicVarIndexingBuilder, "Only builders of the same type can be added together!");

			BasicVarIndexingBuilder that = (BasicVarIndexingBuilder) genericThat;

			final int newDefaultIndex = this.defaultIndex + that.defaultIndex;
			final Map<VarDecl<?>, Integer> newVarToOffset = Containers.createMap();

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

		@Override
		public BasicVarIndexingBuilder sub(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof BasicVarIndexingBuilder, "Only builders of the same type can be subtracted!");

			BasicVarIndexingBuilder that = (BasicVarIndexingBuilder) genericThat;

			final int newDefaultIndex = this.defaultIndex - that.defaultIndex;
			checkArgument(newDefaultIndex >= 0, "Negative default index");
			final Map<VarDecl<?>, Integer> newVarToOffset = Containers.createMap();

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

		@Override
		public BasicVarIndexingBuilder join(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof BasicVarIndexingBuilder, "Only builders of the same type can be joined!");

			BasicVarIndexingBuilder that = (BasicVarIndexingBuilder) genericThat;

			final int newDefaultIndex = max(this.defaultIndex, that.defaultIndex);
			final Map<VarDecl<?>, Integer> newVarToOffset = Containers.createMap();

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

		@Override
		public int get(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			final Integer offset = varToOffset.getOrDefault(varDecl, 0);
			return defaultIndex + offset;
		}

		@Override
		public BasicVarIndexing build() {
			return new BasicVarIndexing(this);
		}

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

}
