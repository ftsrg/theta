package hu.bme.mit.theta.frontend.benchmark.formatters.impl;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.benchmark.formatters.Formatter;

public class LatexFormatter implements Formatter {

	private final Logger logger;
	boolean isFirstCell = true;

	public LatexFormatter(final Logger logger) {
		this.logger = logger;
	}

	@Override
	public Formatter cell(final String text) {
		cell(text, 1);
		return this;
	}

	@Override
	public Formatter cell(String text, final int colspan) {
		text = text.replace("_", "\\_").replace("#", "\\#").replace("%", "\\%");
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
	public Formatter newRow() {
		logger.writeln("\\\\\\hline", 0);
		isFirstCell = true;
		return this;
	}

}
