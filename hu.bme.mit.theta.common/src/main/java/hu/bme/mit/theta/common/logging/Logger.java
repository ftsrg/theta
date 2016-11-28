package hu.bme.mit.theta.common.logging;

public interface Logger {
	default Logger write(final Object obj, final int level) {
		write(obj, level, 0);
		return this;
	}

	Logger write(Object obj, int level, int padding);

	Logger writeln(int level);

	default Logger writeln(final Object obj, final int level) {
		writeln(obj, level, 0);
		return this;
	}

	default Logger writeln(final Object obj, final int level, final int padding) {
		write(obj, level, padding);
		writeln(level);
		return this;
	}

	default Logger writeln(final Object o1, final Object o2, final int level, final int padding) {
		write(o1, level, padding);
		write(o2, level);
		writeln(level);
		return this;
	}

	Logger writeHeader(Object obj, int level);
}
