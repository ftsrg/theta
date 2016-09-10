package hu.bme.mit.theta.splittingcegar.ui.formatters;

public interface Formatter {
	void cell(String text);

	void cell(String text, int colspan);

	void newRow();
}
