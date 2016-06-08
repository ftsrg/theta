package hu.bme.mit.inf.ttmc.formalism.utils;

import java.util.HashMap;
import java.util.Map;
import java.util.StringJoiner;

import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class VarIndexes {

	private final Map<VarDecl<?>, Integer> varToIndex;

	private static final VarIndexes ALL_ZERO;

	static {
		ALL_ZERO = new VarIndexes(new HashMap<>());
	}

	private VarIndexes(final Map<VarDecl<?>, Integer> varToIndex) {
		this.varToIndex = new HashMap<>(varToIndex);
	}

	public static VarIndexes allZero() {
		return ALL_ZERO;
	}

	public int getIndex(final VarDecl<?> varDecl) {
		Integer index = varToIndex.get(varDecl);
		if (index == null) {
			index = 0;
		}
		return index;
	}

	public VarIndexes inc(final VarDecl<?> varDecl) {
		final Map<VarDecl<?>, Integer> newVarToIndex = new HashMap<VarDecl<?>, Integer>(varToIndex);
		final Integer index = newVarToIndex.get(varDecl);

		if (index == null) {
			newVarToIndex.put(varDecl, 1);
		} else {
			newVarToIndex.put(varDecl, index + 1);
		}

		return new VarIndexes(newVarToIndex);
	}

	@Override
	public String toString() {

		final StringJoiner sj = new StringJoiner(", ", "IndexMap(", ")");
		for (final VarDecl<?> varDecl : varToIndex.keySet()) {
			final StringBuilder sb = new StringBuilder();
			sb.append(varDecl.getName());
			sb.append(" -> ");
			sb.append(varToIndex.get(varDecl));
			sj.add(sb);
		}
		return sj.toString();
	}

}
