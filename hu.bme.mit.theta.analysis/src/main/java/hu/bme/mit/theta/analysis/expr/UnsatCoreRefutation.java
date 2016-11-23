package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Iterator;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public class UnsatCoreRefutation implements Refutation, Iterable<Expr<? extends BoolType>> {

	private final Collection<Expr<? extends BoolType>> unsatCore;
	private final int pruneIndex;

	private UnsatCoreRefutation(final Collection<Expr<? extends BoolType>> unsatCore, final int pruneIndex) {
		checkNotNull(unsatCore);
		checkArgument(unsatCore.size() > 0);
		this.unsatCore = ImmutableSet.copyOf(unsatCore);
		this.pruneIndex = pruneIndex;
	}

	public static UnsatCoreRefutation create(final Collection<Expr<? extends BoolType>> unsatCore,
			final int pruneIndex) {
		return new UnsatCoreRefutation(unsatCore, pruneIndex);
	}

	public Collection<Expr<? extends BoolType>> getUnsatCore() {
		return unsatCore;
	}

	@Override
	public Iterator<Expr<? extends BoolType>> iterator() {
		return unsatCore.iterator();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(unsatCore).toString();
	}

	@Override
	public int getPruneIndex() {
		return pruneIndex;
	}
}
