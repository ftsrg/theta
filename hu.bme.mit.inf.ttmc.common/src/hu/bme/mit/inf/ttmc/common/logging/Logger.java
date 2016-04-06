package hu.bme.mit.inf.ttmc.common.logging;

public interface Logger {
	void write(Object obj, int level);
	
	void write(Object obj, int level, int padding);
	
	void writeln(int level);
	
	void writeln(Object obj, int level);

	void writeln(Object obj, int level, int padding);
	
	void writeHeader(Object obj, int level);
}
