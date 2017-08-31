package hu.bme.mit.theta.analysis.cfa.prec;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.cfa.CfaPrec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

/**
 * Represents an immutable constant precision.
 */
public final class ConstCfaPrec<P extends Prec> implements CfaPrec<P> {

	private final P prec;

	private ConstCfaPrec(final P prec) {
		this.prec = checkNotNull(prec);
	}

	public static <P extends Prec> ConstCfaPrec<P> create(final P prec) {
		return new ConstCfaPrec<>(prec);
	}

	public ConstCfaPrec<P> refine(final P refinedPrec) {
		if (this.prec.equals(refinedPrec)) {
			return this;
		} else {
			return create(refinedPrec);
		}
	}

	@Override
	public P getPrec(final Loc loc) {
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
		} else if (obj instanceof ConstCfaPrec) {
			final ConstCfaPrec<?> that = (ConstCfaPrec<?>) obj;
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
