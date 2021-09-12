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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.StringJoiner;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents an immutable mapping, where each variable is associated with an
 * index. The inner builder class can also be used to create a new instance.
 */
public class PushPopVarIndexing implements VarIndexing {
	private final Map<VarDecl<?>, IndexStack> varToIndex;

	private PushPopVarIndexing(final PushPopVarIndexingBuilder builder) {
		varToIndex = ImmutableMap.copyOf(builder.varToIndex);
	}

	/**
	 * Create a new instance
	 *
	 * @return New instance
	 */
	public static PushPopVarIndexing create() {
		return builder().build();
	}

	/**
	 * Create a builder
	 *
	 * @return New builder
	 */
	public static PushPopVarIndexingBuilder builder() {
		return new PushPopVarIndexingBuilder();
	}

	/**
	 * Create a new builder from the current instance.
	 *
	 * @return New builder
	 */
	@Override
	public PushPopVarIndexingBuilder transform() {
		return new PushPopVarIndexingBuilder(this);
	}

	/**
	 * Increment the index of a given variable with a given amount
	 *
	 * @param varDecl Variable to increment
	 * @param n       Amount to increment
	 * @return Transformed indexing
	 */
	@Override
	public PushPopVarIndexing inc(final VarDecl<?> varDecl, final int n) {
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
	public PushPopVarIndexing inc(final VarDecl<?> varDecl) {
		return inc(varDecl, 1);
	}

	/**
	 * Push the variable's index to the stack
	 *
	 * @param varDecl Variable to push
	 * @return Transformed indexing
	 */
	public PushPopVarIndexing push(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		return transform().push(varDecl).build();
	}

	/**
	 * Pop the variable's index from the stack
	 *
	 * @param varDecl Variable to pop
	 * @return Transformed indexing
	 */
	public PushPopVarIndexing pop(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		return transform().pop(varDecl).build();
	}

	/**
	 * Add another indexing to the current instance
	 *
	 * @param indexing Other indexing
	 * @return Sum of the two indexings
	 */
	@Override
	public PushPopVarIndexing add(final VarIndexing indexing) {
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
	public PushPopVarIndexing sub(final VarIndexing indexing) {
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
	public PushPopVarIndexing join(final VarIndexing indexing) {
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
		return Optional.ofNullable(varToIndex.get(varDecl)).map(IndexStack::peek).orElse(0);
	}

	public static class PushPopVarIndexingBuilder implements VarIndexingBuilder {
		private final Map<VarDecl<?>, IndexStack> varToIndex;

		private PushPopVarIndexingBuilder() {
			varToIndex = Containers.createMap();
		}

		private PushPopVarIndexingBuilder(final PushPopVarIndexing indexing) {
			this.varToIndex = Containers.createMap(indexing.varToIndex);
		}

		@Override
		public PushPopVarIndexingBuilder inc(final VarDecl<?> varDecl, final int n) {
			checkNotNull(varDecl);

			if (n != 0) {
				IndexStack currentIndex = varToIndex.get(varDecl);
				if(currentIndex == null) currentIndex = IndexStack.create(n);
				else currentIndex = currentIndex.incCurrent(n);
				varToIndex.put(varDecl, currentIndex);
			}

			return this;
		}

		@Override
		public PushPopVarIndexingBuilder inc(final VarDecl<?> varDecl) {
			return inc(varDecl, 1);
		}

		@Override
		public PushPopVarIndexingBuilder incAll() {
			throw new UnsupportedOperationException("incAll not supported by PushPopVarIndexing!");
		}

		public PushPopVarIndexingBuilder push(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			IndexStack currentIndex = varToIndex.get(varDecl);
			if(currentIndex == null) currentIndex = IndexStack.create(0);
			varToIndex.put(varDecl, currentIndex.push(currentIndex.prevMax + 1));
			return this;
		}

		public PushPopVarIndexingBuilder pop(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			IndexStack currentIndex = varToIndex.get(varDecl);
			if(currentIndex == null) currentIndex = IndexStack.create(0);
			varToIndex.put(varDecl, currentIndex.pop());
			return this;
		}

		@Override
		public PushPopVarIndexingBuilder add(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof PushPopVarIndexingBuilder, "Only builders of the same type can be added together!");

			PushPopVarIndexingBuilder that = (PushPopVarIndexingBuilder) genericThat;

			for (Map.Entry<VarDecl<?>, IndexStack> entry : that.varToIndex.entrySet()) {
				final VarDecl<?> varDecl = entry.getKey();
				final IndexStack thatIndexStack = entry.getValue();
				IndexStack thisIndexStack = varToIndex.getOrDefault(varDecl, IndexStack.create(0));

				int i;
				for (i = 0; i < thatIndexStack.negativeCount; i++) {
					final int idx = thatIndexStack.negativeCount - i;
					thisIndexStack = thisIndexStack.incBelowCurrent(idx, thatIndexStack.indices.get(i));
				}
				thisIndexStack = thisIndexStack.incCurrent(thatIndexStack.indices.get(i));
				for (++i; i < thatIndexStack.indices.size(); i++) {
					thisIndexStack = thisIndexStack.push(thatIndexStack.indices.get(i));
				}

				varToIndex.put(varDecl, thisIndexStack);
			}

			return this;
		}

		@Override
		public PushPopVarIndexingBuilder sub(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof PushPopVarIndexingBuilder, "Only builders of the same type can be subtracted!");

			PushPopVarIndexingBuilder that = (PushPopVarIndexingBuilder) genericThat;

			for (Map.Entry<VarDecl<?>, IndexStack> entry : that.varToIndex.entrySet()) {
				final VarDecl<?> varDecl = entry.getKey();
				final IndexStack thatIndexStack = entry.getValue();
				IndexStack thisIndexStack = varToIndex.getOrDefault(varDecl, IndexStack.create(0));

				int i;
				for (i = 0; i < thatIndexStack.negativeCount; i++) {
					final int idx = thatIndexStack.negativeCount - 1 - i;
					thisIndexStack = thisIndexStack.incBelowCurrent(idx, thatIndexStack.indices.get(i));
				}
				thisIndexStack = thisIndexStack.incCurrent(thatIndexStack.indices.get(i));
				for (++i; i < thatIndexStack.indices.size(); i++) {
					thisIndexStack = thisIndexStack.pop();
				}

				varToIndex.put(varDecl, thisIndexStack);
			}

			return this;
		}

		@Override
		public PushPopVarIndexingBuilder join(final VarIndexingBuilder genericThat) {
			throw new UnsupportedOperationException("Not yet implemented!");
		}

		@Override
		public int get(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			final IndexStack index = varToIndex.get(varDecl);
			if(index == null) return 0;
			else return index.peek();
		}

		@Override
		public PushPopVarIndexing build() {
			return new PushPopVarIndexing(this);
		}

	}

	private static class IndexStack {
		private final int currentHeight;
		private final int negativeCount;
		private final List<Integer> indices;
		private final int prevMax;

		private IndexStack(final int currentHeight, final int negativeCount, final List<Integer> indices, final int prevMax) {
			checkNotNull(indices);
			this.currentHeight = currentHeight;
			this.negativeCount = negativeCount;
			this.indices = ImmutableList.copyOf(indices);
			this.prevMax = prevMax;
		}

		private static IndexStack create(final int firstElement) {
			checkArgument(firstElement >= 0, "Negative indices are not supported!");
			final int newCurrentHeight = 0;
			final List<Integer> newIndices = new ArrayList<>();
			newIndices.add(firstElement);
			return IndexStack.of(newCurrentHeight, 0, newIndices, firstElement);
		}

		private static IndexStack of(final int currentHeight, final int negativeCount, final List<Integer> indices, final int prevMax) {
			return new IndexStack(currentHeight, negativeCount, indices, prevMax);
		}

		private IndexStack push(final int value) {
			checkArgument(value >= 0, "Negative indices are not supported!");
			final int newCurrentHeight = currentHeight + 1;
			final List<Integer> newIndices = new ArrayList<>(indices);
			if(newCurrentHeight > 0) {
				newIndices.add(value);
			} else {
				newIndices.remove(negativeCount + newCurrentHeight);
				newIndices.add(negativeCount + newCurrentHeight, value);
			}
			final int newPrevMax = Math.max(prevMax, value);
			return IndexStack.of(newCurrentHeight, negativeCount, newIndices, newPrevMax);
		}

		private IndexStack pop() {
			final int newCurrentHeight = currentHeight - 1;
			final List<Integer> newIndices = new ArrayList<>(indices);
			int newNegativeCount = negativeCount;
			if (newCurrentHeight >= 0) {
				newIndices.remove(newIndices.size() - 1);
			}
			else if (newNegativeCount < -newCurrentHeight ) {
				newIndices.add(0, 0);
				++newNegativeCount;
			}
			return IndexStack.of(newCurrentHeight, newNegativeCount, newIndices, prevMax);
		}

		private IndexStack incCurrent(final int value) {
			final List<Integer> newIndices = new ArrayList<>(indices);
			checkArgument(prevMax + value >= 0, "Negative indices are not supported!");

			newIndices.remove(negativeCount + currentHeight);
			newIndices.add(negativeCount + currentHeight, prevMax + value);
			final int newPrevMax = prevMax + value;
			return IndexStack.of(currentHeight, negativeCount, newIndices, newPrevMax);
		}

		private IndexStack incBelowCurrent(final int levelOffset, final int value) {
			final List<Integer> newIndices = new ArrayList<>(indices);
			checkArgument(levelOffset > 0, "Level offset must be a positive number!");
			checkArgument(prevMax + value >= 0, "Negative indices are not supported!");
			final int newNegativeCount;
			if(negativeCount + currentHeight - levelOffset < 0) {
				final int abs = Math.abs(negativeCount + currentHeight - levelOffset);
				newIndices.addAll(0, Collections.nCopies(abs, 0));
				newNegativeCount = negativeCount + abs;
			} else {
				newNegativeCount = negativeCount;
			}
			newIndices.remove(newNegativeCount + currentHeight - levelOffset);
			newIndices.add(newNegativeCount + currentHeight - levelOffset, prevMax + value);
			final int newPrevMax = prevMax + value;
			return IndexStack.of(currentHeight, newNegativeCount, newIndices, newPrevMax);
		}

		private int peek() {
			return indices.get(negativeCount + currentHeight);
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "PushPopIndexMap(", ")");
		for (final VarDecl<?> varDecl : varToIndex.keySet()) {
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
