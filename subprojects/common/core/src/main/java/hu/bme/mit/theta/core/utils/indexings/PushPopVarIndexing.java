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

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringJoiner;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static java.lang.Math.max;

/**
 * Represents an immutable mapping, where each variable is associated with a stackable
 * index. The inner builder class can also be used to create a new instance.
 */
public class PushPopVarIndexing implements VarIndexing {
	private static final PushPopVarIndexing ALL_ZERO = new PushPopVarIndexing.PushPopVarIndexingBuilder(0).build();
	private static final PushPopVarIndexing ALL_ONE = new PushPopVarIndexing.PushPopVarIndexingBuilder(1).build();

	private final int defaultIndex;
	private final Map<VarDecl<?>, OffsetStack> varToOffset;

	private PushPopVarIndexing(final PushPopVarIndexing.PushPopVarIndexingBuilder builder) {
		defaultIndex = builder.defaultIndex;
		varToOffset = ImmutableMap.copyOf(builder.varToOffset);
	}

	/**
	 * Create a new instance with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New instance
	 */
	static PushPopVarIndexing all(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		switch (defaultIndex) {
			case 0:
				return ALL_ZERO;
			case 1:
				return ALL_ONE;
			default:
				return new PushPopVarIndexing.PushPopVarIndexingBuilder(defaultIndex).build();
		}
	}

	/**
	 * Create a builder with a default index.
	 *
	 * @param defaultIndex Default index
	 * @return New builder
	 */
	static PushPopVarIndexing.PushPopVarIndexingBuilder builder(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new PushPopVarIndexing.PushPopVarIndexingBuilder(defaultIndex);
	}

	/**
	 * Create a new builder from the current instance.
	 *
	 * @return New builder
	 */
	@Override
	public PushPopVarIndexing.PushPopVarIndexingBuilder transform() {
		return new PushPopVarIndexing.PushPopVarIndexingBuilder(this);
	}

	/**
	 * Increment the index of a given variable by one
	 *
	 * @param varDecl Variable to increment
	 * @return Transformed indexing
	 */
	@Override
	public PushPopVarIndexing inc(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		return transform().inc(varDecl).build();
	}

	/**
	 * Push the offset of the varDecl to stack
	 *
	 * @param varDecl Variable to push
	 * @return Transformed index
	 */
	public PushPopVarIndexing push(final VarDecl<?> varDecl) {
		return transform().push(varDecl).build();
	}

	/**
	 * Pop the offset of the varDecl from stack
	 *
	 * @param varDecl Variable to pop
	 * @return Transformed index
	 */
	public PushPopVarIndexing pop(final VarDecl<?> varDecl) {
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
		final OffsetStack current = varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
		final int offset = current.peek();
		return defaultIndex + offset;
	}

	public static class PushPopVarIndexingBuilder implements VarIndexingBuilder {
		private int defaultIndex;
		private Map<VarDecl<?>, OffsetStack> varToOffset;

		private PushPopVarIndexingBuilder(final int defaultIndex) {
			checkArgument(defaultIndex >= 0, "Negative default index");
			this.defaultIndex = defaultIndex;
			varToOffset = Containers.createMap();
		}

		private PushPopVarIndexingBuilder(final PushPopVarIndexing indexing) {
			this.defaultIndex = indexing.defaultIndex;
			this.varToOffset = Containers.createMap(indexing.varToOffset);
		}

		@Override
		public PushPopVarIndexing.PushPopVarIndexingBuilder inc(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);

			final OffsetStack current = varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
			checkArgument(defaultIndex + current.peek() + 1 >= 0, "Negative index for variable");
			varToOffset.put(varDecl, current.incCurrent());

			return this;
		}

		@Override
		public PushPopVarIndexing.PushPopVarIndexingBuilder incAll() {
			defaultIndex = defaultIndex + 1;
			return this;
		}

		public PushPopVarIndexing.PushPopVarIndexingBuilder push(final VarDecl<?> varDecl) {
			final OffsetStack current = varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
			varToOffset.put(varDecl, current.push());
			return this;
		}

		public PushPopVarIndexing.PushPopVarIndexingBuilder pop(final VarDecl<?> varDecl) {
			final OffsetStack current = varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
			varToOffset.put(varDecl, current.pop());
			return this;
		}

		@Override
		public PushPopVarIndexing.PushPopVarIndexingBuilder add(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof PushPopVarIndexing.PushPopVarIndexingBuilder, "Only builders of the same type can be added together!");

			PushPopVarIndexing.PushPopVarIndexingBuilder that = (PushPopVarIndexing.PushPopVarIndexingBuilder) genericThat;

			final int newDefaultIndex = this.defaultIndex + that.defaultIndex;
			final Map<VarDecl<?>, OffsetStack> newVarToOffset = Containers.createMap();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final OffsetStack offsetStack1 = this.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
				final OffsetStack offsetStack2 = that.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));

				final OffsetStack sum = offsetStack1.add(offsetStack2);
				newVarToOffset.put(varDecl, sum);
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		@Override
		public PushPopVarIndexing.PushPopVarIndexingBuilder sub(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof PushPopVarIndexing.PushPopVarIndexingBuilder, "Only builders of the same type can be added together!");

			PushPopVarIndexing.PushPopVarIndexingBuilder that = (PushPopVarIndexing.PushPopVarIndexingBuilder) genericThat;

			final int newDefaultIndex = this.defaultIndex - that.defaultIndex;
			final Map<VarDecl<?>, OffsetStack> newVarToOffset = Containers.createMap();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final OffsetStack offsetStack1 = this.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
				final OffsetStack offsetStack2 = that.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));

				final OffsetStack sum = offsetStack1.sub(offsetStack2);
				newVarToOffset.put(varDecl, sum);
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		@Override
		public PushPopVarIndexing.PushPopVarIndexingBuilder join(final VarIndexingBuilder genericThat) {
			checkNotNull(genericThat);
			checkArgument(genericThat instanceof PushPopVarIndexing.PushPopVarIndexingBuilder, "Only builders of the same type can be added together!");

			PushPopVarIndexing.PushPopVarIndexingBuilder that = (PushPopVarIndexing.PushPopVarIndexingBuilder) genericThat;

			final int newDefaultIndex = max(this.defaultIndex, that.defaultIndex);
			final Map<VarDecl<?>, OffsetStack> newVarToOffset = Containers.createMap();

			final Set<VarDecl<?>> varDecls = Sets.union(this.varToOffset.keySet(), that.varToOffset.keySet());
			for (final VarDecl<?> varDecl : varDecls) {
				final OffsetStack offsetStack1 = this.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
				final OffsetStack offsetStack2 = that.varToOffset.getOrDefault(varDecl, OffsetStack.create(0));

				final OffsetStack sum = offsetStack1.max(offsetStack2);
				newVarToOffset.put(varDecl, sum);
			}

			this.defaultIndex = newDefaultIndex;
			this.varToOffset = newVarToOffset;
			return this;
		}

		@Override
		public int get(final VarDecl<?> varDecl) {
			checkNotNull(varDecl);
			final OffsetStack current = varToOffset.getOrDefault(varDecl, OffsetStack.create(0));
			final int offset = current.peek();
			return defaultIndex + offset;
		}

		@Override
		public PushPopVarIndexing build() {
			return new PushPopVarIndexing(this);
		}

	}

	private static class OffsetStack {
		private final int currentHeight;
		private final int negativeCount;
		private final List<Integer> offsets;
		private final int prevMax;
		private final int prevMin;

		private OffsetStack(final int currentHeight, final int negativeCount, final List<Integer> offsets, final int prevMax, final int prevMin) {
			checkNotNull(offsets);
			this.currentHeight = currentHeight;
			this.negativeCount = negativeCount;
			this.offsets = ImmutableList.copyOf(offsets);
			this.prevMax = prevMax;
			this.prevMin = prevMin;
		}

		private static OffsetStack create(final int firstElement) {
			final int newCurrentHeight = 0;
			final List<Integer> newIndices = new ArrayList<>();
			newIndices.add(firstElement);
			return OffsetStack.of(newCurrentHeight, 0, newIndices, firstElement, firstElement);
		}

		private static OffsetStack of(final int currentHeight, final int negativeCount, final List<Integer> indices, final int prevMax, final int prevMin) {
			return new OffsetStack(currentHeight, negativeCount, indices, prevMax, prevMin);
		}

		private OffsetStack push() {
			final int newCurrentHeight = currentHeight + 1;
			final int value = prevMax + 1;
			final List<Integer> newIndices = new ArrayList<>(offsets);
			if(newCurrentHeight > 0) {
				newIndices.add(value);
			} else {
				newIndices.remove(negativeCount + newCurrentHeight);
				newIndices.add(negativeCount + newCurrentHeight, value);
			}
			return OffsetStack.of(newCurrentHeight, negativeCount, newIndices, value, prevMin);
		}

		private OffsetStack pop() {
			final int newCurrentHeight = currentHeight - 1;
			final List<Integer> newIndices = new ArrayList<>(offsets);
			int newNegativeCount = negativeCount;
			if (newCurrentHeight >= 0) {
				newIndices.remove(newIndices.size() - 1);
			}
			else if (newNegativeCount < -newCurrentHeight ) {
				newIndices.add(0, 0);
				++newNegativeCount;
			}
			return OffsetStack.of(newCurrentHeight, newNegativeCount, newIndices, prevMax, prevMin);
		}

		private OffsetStack incCurrent() {
			final List<Integer> newIndices = new ArrayList<>(offsets);

			newIndices.remove(negativeCount + currentHeight);
			newIndices.add(negativeCount + currentHeight, prevMax + 1);
			final int newPrevMax = prevMax + 1;
			return OffsetStack.of(currentHeight, negativeCount, newIndices, newPrevMax, prevMin);
		}

		private OffsetStack add(final OffsetStack that) {
			checkArgument(this.currentHeight >= that.negativeCount, "Cannot add stacks due to mismatched depths!");

			int i;
			final List<Integer> newOffsets = new ArrayList<>(this.offsets);
			int newCurrentHeight = this.currentHeight;
			int newPrevMax = this.prevMax;
			for (i = 0; i < that.negativeCount; i++) {
				final int newOffset = this.prevMax + that.offsets.get(i);
				newOffsets.remove(currentHeight - (that.negativeCount - i));
				newOffsets.add(currentHeight - (that.negativeCount - i), newOffset);
				newPrevMax = Math.max(newPrevMax, newOffset);
			}
			if(that.currentHeight >= 0) {
				final int newOffset = this.prevMax + that.offsets.get(i);
				newOffsets.remove(currentHeight);
				newOffsets.add(currentHeight, newOffset);
				newPrevMax = Math.max(newPrevMax, newOffset);
				++i;
				for (; i < that.offsets.size(); ++i) {
					newOffsets.add(this.prevMax + that.offsets.get(i));
					newPrevMax = Math.max(newPrevMax, that.offsets.get(i));
					++newCurrentHeight;
				}
			} else {
				newCurrentHeight+=that.currentHeight;
				for (int i1 = 0; i1 > that.currentHeight; --i1) {
					newOffsets.remove(newOffsets.size() - 1);
				}
			}
			return OffsetStack.of(newCurrentHeight, this.negativeCount, newOffsets, newPrevMax, prevMin);
		}

		private OffsetStack sub(final OffsetStack that) {
			int i;
			final List<Integer> newOffsets = new ArrayList<>(this.offsets);
			int newCurrentHeight = this.currentHeight;
			int newPrevMin = this.prevMin;
			int newNegativeCount = negativeCount;
			if(this.currentHeight < that.currentHeight) {
				int toAdd = that.currentHeight - this.currentHeight;
				newNegativeCount+=toAdd;
				for (int i1 = 0; i1 < toAdd; i1++) {
					newOffsets.add(0, 0);
				}
			}
			int savedNegativeCount = newNegativeCount;
			final int toPop = Math.max(that.currentHeight, 0);
			for (i = 0; i < that.negativeCount; i++) {
				final int newOffset = prevMin - that.offsets.get(i);
				if(savedNegativeCount + currentHeight - toPop - (that.negativeCount - i) >= 0) {
					newOffsets.remove(savedNegativeCount + currentHeight - toPop - (that.negativeCount - i));
					newOffsets.add(savedNegativeCount + currentHeight - toPop - (that.negativeCount - i), newOffset);
				} else {
					newOffsets.add(0, newOffset);
					++newNegativeCount;
				}
				newPrevMin = Math.min(newPrevMin, newOffset);
			}
			if(that.currentHeight >= 0) {
				final int newOffset = prevMin - that.offsets.get(i);
				newOffsets.remove(savedNegativeCount + currentHeight - toPop);
				newOffsets.add(savedNegativeCount + currentHeight - toPop, newOffset);
				newPrevMin = Math.min(newPrevMin, newOffset);
				++i;
				for (int i1 = toPop; i1 > 0; --i1) {
					newOffsets.remove(i1);
				}
				newCurrentHeight-=toPop;
			}
			return OffsetStack.of(newCurrentHeight, newNegativeCount, newOffsets, prevMax, newPrevMin);
		}

		private OffsetStack max(final OffsetStack that) {
			checkState(this.offsets.size() == that.offsets.size() && this.currentHeight == that.currentHeight && this.negativeCount == that.negativeCount, "Only stacks of the same sizes can be joined!");
			final List<Integer> newOffsets = new ArrayList<>();
			List<Integer> integers = this.offsets;
			for (int i = 0; i < integers.size(); i++) {
				Integer offset = integers.get(i);
				newOffsets.add(Math.max(offset, that.offsets.get(i)));
			}
			return OffsetStack.of(currentHeight, negativeCount, newOffsets, Math.max(prevMax, that.prevMax), Math.min(prevMin, that.prevMin));
		}

		private int peek() {
			return offsets.get(negativeCount + currentHeight);
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "PushPopIndexMap(" + defaultIndex + ", ", ")");
		for (final VarDecl<?> varDecl : varToOffset.keySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(varDecl.getName());
			sb.append(" -> ");
			final OffsetStack offsetStack = varToOffset.get(varDecl);
			final List<Integer> offsets = offsetStack.offsets;
			final StringJoiner stack = new StringJoiner(", ", "[", "]");
			for (int i = 0; i < offsets.size(); i++) {
				Integer offset = offsets.get(i);
				final StringBuilder innerSb = new StringBuilder();
				innerSb.append(i - offsetStack.negativeCount);
				innerSb.append(": ");
				innerSb.append(offset);
				stack.add(innerSb.toString());
			}
			sb.append(stack);
			sj.add(sb);
		}
		return sj.toString();
	}

	////

}
