package hu.bme.mit.theta.common.table.impl;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.table.TableWriter;

public class SimpleTableWriter implements TableWriter {

	private final Logger logger;
	private final String delimeter;

	public SimpleTableWriter(final Logger logger, final String delimeter) {
		this.logger = logger;
		this.delimeter = delimeter;
	}

	public SimpleTableWriter(final Logger logger) {
		this(logger, ",");
	}

	boolean isFirstCell = true;

	@Override
	public TableWriter cell(final Object obj, final int colspan) {
		if (!isFirstCell)
			logger.write(delimeter, 0);
		logger.write(obj, 0);
		for (int i = 0; i < colspan - 1; ++i)
			logger.write(delimeter, 0);
		isFirstCell = false;
		return this;
	}

	@Override
	public TableWriter newRow() {
		logger.writeln(0);
		isFirstCell = true;
		return this;
	}

}
