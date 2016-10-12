package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

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

	public static ItpRefutation createSequence(final List<Expr<? extends BoolType>> itpSequence) {
		return new ItpRefutation(itpSequence);
	}

	public static ItpRefutation createCraig(final Expr<? extends BoolType> itp, final int i, final int n) {
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
		final StringBuilder sb = new StringBuilder();
		sb.append("ItpRefutation(");
		for (int i = 0; i < size(); ++i) {
			sb.append(get(i).toString());
			if (i < size() - 1)
				sb.append("; ");
		}
		sb.append(")");
		return sb.toString();
	}
}
