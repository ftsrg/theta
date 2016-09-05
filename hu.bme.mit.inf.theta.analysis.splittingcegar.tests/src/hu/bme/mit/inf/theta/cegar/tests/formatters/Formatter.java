package hu.bme.mit.inf.theta.cegar.tests.formatters;

public interface Formatter {
	void cell(String text);
	
	void cell(String text, int colspan);
	
	void newRow();
}
