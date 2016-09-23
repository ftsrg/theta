package hu.bme.mit.theta.core.utils.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.theta.core.decl.VarDecl;

public class VarIndexes {

	private final int defaultIndex;
	private final Map<VarDecl<?>, Integer> varToOffset;

	private VarIndexes(final Builder builder) {
		defaultIndex = builder.defaultIndex;
		varToOffset = builder.varToOffset;
	}

	public static VarIndexes all(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new Builder(defaultIndex).build();
	}

	public static Builder builder(final int defaultIndex) {
		checkArgument(defaultIndex >= 0);
		return new Builder(defaultIndex);
	}

	public Builder transform() {
		return new Builder(this);
	}

	public VarIndexes inc(final VarDecl<?> varDecl) {
		checkNotNull(varDecl);
		return transform().inc(varDecl).build();
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
		private final Map<VarDecl<?>, Integer> varToOffset;

		private Builder(final int defaultIndex) {
			checkArgument(defaultIndex >= 0);
			this.defaultIndex = defaultIndex;
			varToOffset = new HashMap<>();
		}

		private Builder(final VarIndexes varIndexes) {
			this.defaultIndex = varIndexes.defaultIndex;
			this.varToOffset = new HashMap<>(varIndexes.varToOffset);
		}

		public Builder inc(final VarDecl<?> varDecl) {
			final Integer offset = varToOffset.get(varDecl);
			if (offset == null) {
				varToOffset.put(varDecl, 1);
			} else {
				varToOffset.put(varDecl, offset + 1);
			}
			return this;
		}

		public Builder incAll() {
			defaultIndex = defaultIndex + 1;
			return this;
		}

		public VarIndexes build() {
			return new VarIndexes(this);
		}

	}

}
