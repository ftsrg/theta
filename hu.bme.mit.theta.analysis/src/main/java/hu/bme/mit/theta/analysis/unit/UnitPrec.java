package hu.bme.mit.theta.analysis.unit;

import hu.bme.mit.theta.analysis.Prec;

public final class UnitPrec implements Prec {

	private static final UnitPrec INSTANCE = new UnitPrec();

	private UnitPrec() {
	}

	public static UnitPrec getInstance() {
		return INSTANCE;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
