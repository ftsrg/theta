package hu.bme.mit.theta.formalism.utils;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.theta.formalism.common.decl.VarDecl;

public class VarIndexes {

	private final int defaultIndex;
	private final Map<VarDecl<?>, Integer> varToIndex;

	private VarIndexes(final Builder builder) {
		defaultIndex = builder.defaultIndex;
		varToIndex = builder.varToIndex;
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
		Integer index = varToIndex.get(varDecl);
		if (index == null) {
			index = defaultIndex;
		}
		return index;
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "IndexMap(", ")");
		sj.add(Integer.toString(defaultIndex));
		for (final VarDecl<?> varDecl : varToIndex.keySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(varDecl.getName());
			sb.append(" -> ");
			sb.append(varToIndex.get(varDecl));
			sj.add(sb);
		}
		return sj.toString();
	}

	////

	public static final class Builder {
		private int defaultIndex;
		private final Map<VarDecl<?>, Integer> varToIndex;

		private Builder(final int defaultIndex) {
			checkArgument(defaultIndex >= 0);
			this.defaultIndex = defaultIndex;
			varToIndex = new HashMap<>();
		}

		private Builder(final VarIndexes varIndexes) {
			this.defaultIndex = varIndexes.defaultIndex;
			this.varToIndex = new HashMap<>(varIndexes.varToIndex);
		}

		public Builder inc(final VarDecl<?> varDecl) {
			final Integer index = varToIndex.get(varDecl);
			if (index == null) {
				varToIndex.put(varDecl, defaultIndex + 1);
			} else {
				varToIndex.put(varDecl, index + 1);
			}
			return this;
		}

		public Builder incAll() {
			for (final VarDecl<?> varDecl : varToIndex.keySet()) {
				final int index = varToIndex.get(varDecl);
				varToIndex.put(varDecl, index + 1);
			}
			defaultIndex = defaultIndex + 1;
			return this;
		}

		public VarIndexes build() {
			return new VarIndexes(this);
		}

	}

}
