package hu.bme.mit.theta.common.logging.impl;

import hu.bme.mit.theta.common.logging.Logger;

public final class ConsoleLogger extends MinLevelBasedLogger {

	public ConsoleLogger(final int minLevel) {
		super(minLevel);
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i)
				System.out.print("   ");
			System.out.print(obj);
		}
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		if (level <= minLevel)
			System.out.println();
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			System.out.println();
			System.out.println("----------" + obj + "----------");
		}
		return this;
	}

}
