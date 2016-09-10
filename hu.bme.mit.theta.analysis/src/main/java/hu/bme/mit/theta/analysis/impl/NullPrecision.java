package hu.bme.mit.theta.analysis.impl;

import hu.bme.mit.theta.analysis.Precision;

public final class NullPrecision implements Precision {

	private static final NullPrecision INSTANCE = new NullPrecision();

	private NullPrecision() {
	}

	public static NullPrecision getInstance() {
		return INSTANCE;
	}

}
