package hu.bme.mit.theta.common.logging.impl;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.common.logging.Logger;

public final class CompositeLogger implements Logger {
	private Collection<Logger> loggers;

	public CompositeLogger(Logger[] loggers) {
		this.loggers = new ArrayList<>(loggers.length);
		for(int i=0;i<loggers.length;++i) this.loggers.add(loggers[i]);
	}
	
	public CompositeLogger(Collection<Logger> loggers) {
		this.loggers = new ArrayList<>(loggers);
	}

	@Override
	public void write(Object obj, int level) {
		for(Logger logger : loggers) logger.write(obj, level);
	}

	@Override
	public void write(Object obj, int level, int padding) {
		for(Logger logger : loggers) logger.write(obj, level, padding);
	}

	@Override
	public void writeln(int level) {
		for(Logger logger : loggers) logger.writeln(level);
	}

	@Override
	public void writeln(Object obj, int level) {
		for(Logger logger : loggers) logger.writeln(obj, level);
	}

	@Override
	public void writeln(Object obj, int level, int padding) {
		for(Logger logger : loggers) logger.writeln(obj, level, padding);
	}

	@Override
	public void writeHeader(Object obj, int level) {
		for(Logger logger : loggers) logger.writeHeader(obj, level);
	}

}
