package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

/**
 * Represents an immutable constant precision.
 */
public final class ConstLocPrec<P extends Prec> implements LocPrec<P> {

	private final P prec;

	private ConstLocPrec(final P prec) {
		this.prec = checkNotNull(prec);
	}

	public static <P extends Prec> ConstLocPrec<P> create(final P prec) {
		return new ConstLocPrec<>(prec);
	}

	public ConstLocPrec<P> refine(final P refinedPrec) {
		if (this.prec == refinedPrec) {
			return this;
		} else {
			return create(refinedPrec);
		}
	}

	@Override
	public P getPrec(final CfaLoc loc) {
		checkNotNull(loc);
		return prec;
	}

	public P getPrec() {
		return prec;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(prec).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ConstLocPrec) {
			final ConstLocPrec<?> that = (ConstLocPrec<?>) obj;
			return this.prec.equals(that.prec);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * prec.hashCode();
	}

}
