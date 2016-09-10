package hu.bme.mit.theta.splittingcegar.ui.formatters.impl;

import hu.bme.mit.theta.splittingcegar.ui.formatters.Formatter;

public class ExcelFormatter implements Formatter {

	boolean isFirstCell = true;

	@Override
	public void cell(final String text) {
		cell(text, 1);
	}

	@Override
	public void cell(final String text, final int colspan) {
		if (!isFirstCell)
			System.out.print('\t');
		System.out.print(text);
		for (int i = 0; i < colspan - 1; ++i)
			System.out.print('\t');
		isFirstCell = false;
	}

	@Override
	public void newRow() {
		System.out.println();
		isFirstCell = true;
	}

}
