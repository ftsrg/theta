package hu.bme.mit.theta.common.logging.impl;

import hu.bme.mit.theta.common.logging.Logger;

public abstract class MinLevelBasedLogger implements Logger {
	protected int minLevel; // Only write below this level

	public MinLevelBasedLogger(final int minLevel) {
		this.minLevel = minLevel;
	}

	@Override
	public Logger write(final Object obj, final int level) {
		write(obj, level, 0);
		return this;
	}

	@Override
	public Logger writeln(final Object obj, final int level) {
		writeln(obj, level, 0);
		return this;
	}
}
