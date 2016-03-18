package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

/**
 * Null logger, which does not write anything
 * @author Akos
 */
public class NullLogger implements ILogger {

	@Override
	public void write(Object obj, int level) { }

	@Override
	public void write(Object obj, int level, int padding) { }

	@Override
	public void writeln(int level) { }

	@Override
	public void writeln(Object obj, int level) { }

	@Override
	public void writeln(Object obj, int level, int padding) { }

	@Override
	public void writeTitle(Object obj, int level) { }

}
