package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.utils.impl.IndexedVars;

public final class VarSetsRefutation implements Refutation {

	private final IndexedVars varSets;
	private final int pruneIndex;

	private VarSetsRefutation(final IndexedVars varSets) {
		checkNotNull(varSets);
		checkArgument(!varSets.isEmpty());
		this.varSets = varSets;
		int i = 0;
		while (varSets.getVars(i).isEmpty()) {
			++i;
		}
		this.pruneIndex = i;
	}

	public static VarSetsRefutation create(final IndexedVars varSets) {
		return new VarSetsRefutation(varSets);
	}

	public IndexedVars getVarSets() {
		return varSets;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(varSets).toString();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}
}
