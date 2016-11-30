package hu.bme.mit.theta.frontend.benchmark.formatters;

public interface Formatter {
	Formatter cell(String text);

	Formatter cell(String text, int colspan);

	Formatter newRow();
}
