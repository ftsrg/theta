package hu.bme.mit.theta.analysis.impl;

import hu.bme.mit.theta.analysis.Prec;

public final class NullPrec implements Prec {

	private static final NullPrec INSTANCE = new NullPrec();

	private NullPrec() {
	}

	public static NullPrec getInstance() {
		return INSTANCE;
	}

	@Override
	public String toString() {
		return "NullPrecision";
	}
}
