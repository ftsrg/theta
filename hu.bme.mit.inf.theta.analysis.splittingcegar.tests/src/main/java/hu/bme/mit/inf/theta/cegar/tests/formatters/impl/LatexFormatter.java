package hu.bme.mit.inf.theta.cegar.tests.formatters.impl;

import hu.bme.mit.inf.theta.cegar.tests.formatters.Formatter;

public class LatexFormatter implements Formatter {

	boolean isFirstCell = true;
	
	@Override
	public void cell(String text) {
		cell(text, 1);
	}

	@Override
	public void cell(String text, int colspan) {
		text = text.replace("_", "\\_").replace("#", "\\#").replace("%", "\\%");
		if (!isFirstCell) System.out.print(" & ");
		if (colspan != 1)
			System.out.print("\\multicolumn{" + colspan + "}{c}{" + text + "}");
		else 
			System.out.print(text);
		isFirstCell = false;
	}

	@Override
	public void newRow() {
		System.out.println("\\\\\\hline");
		isFirstCell = true;
	}

}
