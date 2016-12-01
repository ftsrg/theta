package hu.bme.mit.theta.common.logging.impl;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.common.logging.Logger;

public final class CompositeLogger implements Logger {
	private final Collection<Logger> loggers;

	public CompositeLogger(final Logger[] loggers) {
		this.loggers = new ArrayList<>(loggers.length);
		for (int i = 0; i < loggers.length; ++i)
			this.loggers.add(loggers[i]);
	}

	public CompositeLogger(final Collection<Logger> loggers) {
		this.loggers = new ArrayList<>(loggers);
	}

	@Override
	public void write(final Object obj, final int level) {
		for (final Logger logger : loggers)
			logger.write(obj, level);
	}

	@Override
	public void write(final Object obj, final int level, final int padding) {
		for (final Logger logger : loggers)
			logger.write(obj, level, padding);
	}

	@Override
	public void writeln(final int level) {
		for (final Logger logger : loggers)
			logger.writeln(level);
	}

	@Override
	public void writeln(final Object obj, final int level) {
		for (final Logger logger : loggers)
			logger.writeln(obj, level);
	}

	@Override
	public void writeln(final Object obj, final int level, final int padding) {
		for (final Logger logger : loggers)
			logger.writeln(obj, level, padding);
	}

	@Override
	public void writeHeader(final Object obj, final int level) {
		for (final Logger logger : loggers)
			logger.writeHeader(obj, level);
	}

}
