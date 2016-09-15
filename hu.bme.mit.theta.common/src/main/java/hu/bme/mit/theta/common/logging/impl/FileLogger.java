package hu.bme.mit.theta.common.logging.impl;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

import hu.bme.mit.theta.common.logging.Logger;

public final class FileLogger extends MinLevelBasedLogger implements Logger {
	private final PrintWriter pw;
	private final boolean instantFlush;

	public FileLogger(final int minLevel, final String fileName, final boolean instantFlush)
			throws FileNotFoundException {
		super(minLevel);
		pw = new PrintWriter(fileName);
		this.instantFlush = instantFlush;
	}

	@Override
	public void write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i)
				pw.print("   ");
			pw.print(obj);
			if (instantFlush)
				pw.flush();
		}
	}

	@Override
	public void writeln(final int level) {
		if (level <= minLevel) {
			pw.println();
			if (instantFlush)
				pw.flush();
		}
	}

	@Override
	public void writeln(final Object obj, final int level, final int padding) {
		write(obj, level, padding);
		writeln(level);
	}

	@Override
	public void writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			pw.println();
			pw.println("----------" + obj + "----------");
			if (instantFlush)
				pw.flush();
		}
	}

	public void close() {
		pw.close();
	}

}
