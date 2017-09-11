package hu.bme.mit.theta.formalism.cfa.analysis.prec;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaPrec;

/**
 * Represents an immutable global precision that maps the same precision to each
 * location. A refiner is also implemented.
 *
 * @see GlobalCfaPrecRefiner
 */
public final class GlobalCfaPrec<P extends Prec> implements CfaPrec<P> {

	private final P prec;

	private GlobalCfaPrec(final P prec) {
		this.prec = checkNotNull(prec);
	}

	public static <P extends Prec> GlobalCfaPrec<P> create(final P prec) {
		return new GlobalCfaPrec<>(prec);
	}

	public GlobalCfaPrec<P> refine(final P refinedPrec) {
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
		return Utils.toStringBuilder(getClass().getSimpleName()).add(prec).toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof GlobalCfaPrec) {
			final GlobalCfaPrec<?> that = (GlobalCfaPrec<?>) obj;
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
