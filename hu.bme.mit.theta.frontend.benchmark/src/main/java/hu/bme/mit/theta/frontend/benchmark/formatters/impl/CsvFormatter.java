package hu.bme.mit.theta.frontend.benchmark.formatters.impl;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.benchmark.formatters.Formatter;

public class CsvFormatter implements Formatter {

	private final Logger logger;
	private final String delimeter;

	public CsvFormatter(final Logger logger, final String delimeter) {
		this.logger = logger;
		this.delimeter = delimeter;
	}

	public CsvFormatter(final Logger logger) {
		this(logger, ",");
	}

	boolean isFirstCell = true;

	@Override
	public Formatter cell(final String text) {
		cell(text, 1);
		return this;
	}

	@Override
	public Formatter cell(final String text, final int colspan) {
		if (!isFirstCell)
			logger.write(delimeter, 0);
		logger.write(text, 0);
		for (int i = 0; i < colspan - 1; ++i)
			logger.write(delimeter, 0);
		isFirstCell = false;
		return this;
	}

	@Override
	public Formatter newRow() {
		logger.writeln(0);
		isFirstCell = true;
		return this;
	}

}
