package hu.bme.mit.theta.core.utils.impl;

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

public class VarIndexing {

	private static final VarIndexing ALL_ZERO = new Builder(0).build();
	private static final VarIndexing ALL_ONE = new Builder(1).build();

	private final int defaultIndex;
	private final Map<VarDecl<?>, Integer> varToOffset;

	private VarIndexing(final Builder builder) {
		defaultIndex = builder.defaultIndex;
		varToOffset = ImmutableMap.copyOf(builder.varToOffset);
	}

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

	public static Builder builder(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new Builder(defaultIndex);
	}

	public Builder transform() {
		return new Builder(this);
	}

	public VarIndexing inc(final VarDecl<?> varDecl, final int n) {
		checkNotNull(varDecl);
		checkArgument(n >= 0);
		return transform().inc(varDecl, n).build();
	}

	public VarIndexing inc(final VarDecl<?> varDecl) {
		return inc(varDecl, 1);
	}

	public VarIndexing join(final VarIndexing indexing) {
		checkNotNull(indexing);
		return transform().join(indexing.transform()).build();
	}

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
			checkArgument(defaultIndex >= 0);
			this.defaultIndex = defaultIndex;
			varToOffset = new HashMap<>();
		}

		private Builder(final VarIndexing indexing) {
			this.defaultIndex = indexing.defaultIndex;
			this.varToOffset = new HashMap<>(indexing.varToOffset);
		}

		public Builder inc(final VarDecl<?> varDecl, final int n) {
			checkNotNull(varDecl);
			checkArgument(n >= 0);

			if (n > 0) {
				final Integer offset = varToOffset.getOrDefault(varDecl, 0);
				varToOffset.put(varDecl, offset + n);
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
				if (newOffset > 0) {
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
