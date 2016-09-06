package hu.bme.mit.inf.theta.common.logging.impl;

import hu.bme.mit.inf.theta.common.logging.Logger;

public abstract class MinLevelBasedLogger implements Logger {
	protected int minLevel; // Only write below this level
	
	public MinLevelBasedLogger(int minLevel) {
		this.minLevel = minLevel;
	}
	
	@Override
	public void write(Object obj, int level) {
		write(obj, level, 0);
	}

	@Override
	public void writeln(Object obj, int level) {
		writeln(obj, level, 0);
	}
}
