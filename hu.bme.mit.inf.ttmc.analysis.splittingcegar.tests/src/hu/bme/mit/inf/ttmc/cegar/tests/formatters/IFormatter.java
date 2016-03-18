package hu.bme.mit.inf.ttmc.cegar.tests.formatters;

public interface IFormatter {
	void cell(String text);
	
	void cell(String text, int colspan);
	
	void newRow();
}
