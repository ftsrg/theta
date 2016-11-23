package hu.bme.mit.theta.common.logging.impl;

public final class ConsoleLogger extends MinLevelBasedLogger {

	public ConsoleLogger(final int minLevel) {
		super(minLevel);
	}

	@Override
	public void write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i)
				System.out.print("   ");
			System.out.print(obj);
		}
	}

	@Override
	public void writeln(final int level) {
		if (level <= minLevel)
			System.out.println();
	}

	@Override
	public void writeln(final Object obj, final int level, final int padding) {
		write(obj, level, padding);
		writeln(level);
	}

	@Override
	public void writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			System.out.println();
			System.out.println("----------" + obj + "----------");
		}
	}

}
