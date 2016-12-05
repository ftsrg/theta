package hu.bme.mit.theta.common.table.impl;

import java.io.PrintStream;

import hu.bme.mit.theta.common.table.TableWriter;

/**
 * A simple table writer that prints tables to a PrintStream using an arbitrary
 * delimeter and a cell pre/postfix.
 *
 * For exemple in ordinary CSV files, the delimeter is ',' and the pre/postfix
 * is '"'.
 */
public final class SimpleTableWriter implements TableWriter {

	private final PrintStream stream;
	private final String delimeter;
	private final String prefix;
	private final String postfix;
	private boolean isFirstCell = true;

	public SimpleTableWriter(final PrintStream stream, final String delimeter, final String prefix,
			final String postfix) {
		this.stream = stream;
		this.delimeter = delimeter;
		this.prefix = prefix;
		this.postfix = postfix;
	}

	public SimpleTableWriter(final PrintStream stream, final String delimeter) {
		this(stream, delimeter, "", "");
	}

	public SimpleTableWriter(final PrintStream stream) {
		this(stream, ",");
	}

	public SimpleTableWriter() {
		this(System.out);
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		if (!isFirstCell) {
			stream.print(delimeter);
		}
		stream.print(prefix);
		stream.print(obj);
		stream.print(postfix);
		for (int i = 0; i < colspan - 1; ++i) {
			stream.print(delimeter);
		}
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
