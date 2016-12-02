package hu.bme.mit.theta.common.table.impl;

import java.io.PrintStream;

import hu.bme.mit.theta.common.table.TableWriter;

/**
 * A simple table writer that prints tables to a PrintStream using an arbitrary
 * delimeter.
 */
public class SimpleTableWriter implements TableWriter {

	private final PrintStream stream;
	private final String delimeter;

	public SimpleTableWriter(final PrintStream stream, final String delimeter) {
		this.stream = stream;
		this.delimeter = delimeter;
	}

	public SimpleTableWriter(final PrintStream stream) {
		this(stream, ",");
	}

	public SimpleTableWriter() {
		this(System.out);
	}

	boolean isFirstCell = true;

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		if (!isFirstCell)
			stream.print(delimeter);
		stream.print(obj);
		for (int i = 0; i < colspan - 1; ++i)
			stream.print(delimeter);
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		stream.println();
		isFirstCell = true;
		return this;
	}

}
