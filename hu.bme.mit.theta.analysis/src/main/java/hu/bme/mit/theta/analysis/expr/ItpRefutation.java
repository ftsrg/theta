package hu.bme.mit.theta.analysis.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;

public final class ItpRefutation implements Refutation, Iterable<Expr<? extends BoolType>> {

	private final List<Expr<? extends BoolType>> itpSequence;

	private ItpRefutation(final List<Expr<? extends BoolType>> itpSequence) {
		checkNotNull(itpSequence);
		checkArgument(itpSequence.size() > 0);
		this.itpSequence = Collections.unmodifiableList(itpSequence);
	}

	public static ItpRefutation sequence(final List<Expr<? extends BoolType>> itpSequence) {
		return new ItpRefutation(itpSequence);
	}

	public static ItpRefutation craig(final Expr<? extends BoolType> itp, final int i, final int n) {
		checkNotNull(itp);
		checkArgument(n > 0);
		checkArgument(0 <= i && i < n);
		final List<Expr<? extends BoolType>> itpSequence = new ArrayList<>(n);
		for (int k = 0; k < n; ++k) {
			if (k < i) {
				itpSequence.add(Exprs.True());
			} else if (k > i) {
				itpSequence.add(Exprs.False());
			} else {
				itpSequence.add(itp);
			}
		}
		return new ItpRefutation(itpSequence);
	}

	public int size() {
		return itpSequence.size();
	}

	public Expr<? extends BoolType> get(final int i) {
		checkArgument(0 <= i);
		checkArgument(i < size());
		return itpSequence.get(i);
	}

	@Override
	public Iterator<Expr<? extends BoolType>> iterator() {
		return itpSequence.iterator();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).addAll(itpSequence).toString();
	}

	public Stream<Expr<? extends BoolType>> stream() {
		return itpSequence.stream();
	}
}
