package hu.bme.mit.inf.theta.analysis.splittingcegar.ui.formatters;

public interface Formatter {
	void cell(String text);

	void cell(String text, int colspan);

	void newRow();
}
