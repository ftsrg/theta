package hu.bme.mit.inf.theta.analysis.impl;

import hu.bme.mit.inf.theta.analysis.Precision;

public class NullPrecision implements Precision {

	private static final NullPrecision INSTANCE;

	private NullPrecision() {
	}

	static {
		INSTANCE = new NullPrecision();
	}

	public static NullPrecision get() {
		return INSTANCE;
	}

}
