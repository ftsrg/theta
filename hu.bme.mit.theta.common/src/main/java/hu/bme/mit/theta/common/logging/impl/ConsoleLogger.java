package hu.bme.mit.theta.common.logging.impl;

import java.io.PrintStream;

import hu.bme.mit.theta.common.logging.Logger;

public final class ConsoleLogger extends MinLevelBasedLogger {

	private static final PrintStream CONSOLE = System.out;

	public ConsoleLogger(final int minLevel) {
		super(minLevel);
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i)
				CONSOLE.print("|   ");
			CONSOLE.print(obj);
		}
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		if (level <= minLevel)
			CONSOLE.println();
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			CONSOLE.println();
			CONSOLE.println("----------" + obj + "----------");
		}
		return this;
	}

}
