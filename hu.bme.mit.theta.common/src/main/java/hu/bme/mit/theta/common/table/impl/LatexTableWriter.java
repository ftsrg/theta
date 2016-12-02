package hu.bme.mit.theta.common.table.impl;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.table.TableWriter;

public class LatexTableWriter implements TableWriter {

	private final Logger logger;
	boolean isFirstCell = true;

	public LatexTableWriter(final Logger logger) {
		this.logger = logger;
	}

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		final String text = obj.toString().replace("_", "\\_").replace("#", "\\#").replace("%", "\\%");
		if (!isFirstCell)
			logger.write(" & ", 0);
		if (colspan != 1)
			logger.write("\\multicolumn{" + colspan + "}{c}{" + text + "}", 0);
		else
			logger.write(text, 0);
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		logger.writeln("\\\\\\hline", 0);
		isFirstCell = true;
		return this;
	}

}
