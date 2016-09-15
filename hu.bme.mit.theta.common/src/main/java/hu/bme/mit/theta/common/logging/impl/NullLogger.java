package hu.bme.mit.theta.common.logging.impl;

import hu.bme.mit.theta.common.logging.Logger;

public class NullLogger implements Logger {

	@Override
	public void write(final Object obj, final int level) {
	}

	@Override
	public void write(final Object obj, final int level, final int padding) {
	}

	@Override
	public void writeln(final int level) {
	}

	@Override
	public void writeln(final Object obj, final int level) {
	}

	@Override
	public void writeln(final Object obj, final int level, final int padding) {
	}

	@Override
	public void writeHeader(final Object obj, final int level) {
	}

}
