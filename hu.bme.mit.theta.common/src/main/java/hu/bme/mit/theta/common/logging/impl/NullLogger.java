package hu.bme.mit.theta.common.logging.impl;

import hu.bme.mit.theta.common.logging.Logger;

public final class NullLogger implements Logger {

	private static final class LazyHolder {
		private static final NullLogger INSTANCE = new NullLogger();
	}

	private NullLogger() {
	}

	public static NullLogger getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		return this;
	}

}
