package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.utils.impl.IndexedVars;

/**
 * A variable-based refutation that is a sequence of sets of variables.
 */
public final class VarsRefutation implements Refutation {

	private final IndexedVars indexedVars;
	private final int pruneIndex;

	private VarsRefutation(final IndexedVars indexedVars) {
		checkNotNull(indexedVars);
		checkArgument(!indexedVars.isEmpty(), "Trying to create refutation with empty set of variables");
		this.indexedVars = indexedVars;
		int i = 0;
		while (indexedVars.getVars(i).isEmpty()) {
			++i;
		}
		this.pruneIndex = i;
	}

	public static VarsRefutation create(final IndexedVars indexedVars) {
		return new VarsRefutation(indexedVars);
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
