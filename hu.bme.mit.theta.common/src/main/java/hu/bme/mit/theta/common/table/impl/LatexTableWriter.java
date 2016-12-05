package hu.bme.mit.theta.common.table.impl;

import java.io.PrintStream;

import hu.bme.mit.theta.common.table.TableWriter;

/**
 * Table writer that prints tables to a PrintStream in LaTeX format.
 */
public final class LatexTableWriter implements TableWriter {

	private final PrintStream stream;
	private boolean isFirstCell = true;

	public LatexTableWriter(final PrintStream stream) {
		this.stream = stream;
	}

	public LatexTableWriter() {
		this(System.out);
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		final String text = obj.toString().replace("_", "\\_").replace("#", "\\#").replace("%", "\\%");
		if (!isFirstCell)
			stream.print(" & ");
		if (colspan != 1)
			stream.print("\\multicolumn{" + colspan + "}{c}{" + text + "}");
		else
			stream.print(text);
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		stream.println("\\\\\\hline");
		isFirstCell = true;
		return this;
	}

}
