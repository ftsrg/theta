package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.utils.impl.IndexedVars;

public final class IndexedVarsRefutation implements Refutation {

	private final IndexedVars indexedVars;
	private final int pruneIndex;

	private IndexedVarsRefutation(final IndexedVars indexedVars) {
		checkNotNull(indexedVars);
		checkArgument(!indexedVars.isEmpty());
		this.indexedVars = indexedVars;
		int i = 0;
		while (indexedVars.getVars(i).isEmpty()) {
			++i;
		}
		this.pruneIndex = i;
	}

	public static IndexedVarsRefutation create(final IndexedVars indexedVars) {
		return new IndexedVarsRefutation(indexedVars);
	}

	public IndexedVars getVarSets() {
		return indexedVars;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(indexedVars).toString();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}
}
