package hu.bme.mit.theta.common.logging;

public interface Logger {
	Logger write(Object obj, int level);

	Logger write(Object obj, int level, int padding);

	Logger writeln(int level);

	Logger writeln(Object obj, int level);

	Logger writeln(Object obj, int level, int padding);

	Logger writeHeader(Object obj, int level);
}
