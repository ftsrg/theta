package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

/**
 * File logger
 * @author Akos
 */
public class FileLogger extends LoggerBase {
	private PrintWriter pw;
	
	/**
	 * Constructor
	 * @param minLevel Write only below this level
	 * @throws FileNotFoundException 
	 */
	public FileLogger(int minLevel, String fileName) throws FileNotFoundException {
		super(minLevel);
		pw = new PrintWriter(fileName);
	}

	@Override
	public void write(Object obj, int level, int padding) {
		if(level <= minLevel){
			for(int i = 0; i < padding; ++i) pw.print("   ");
			pw.print(obj);
		}
	}

	@Override
	public void writeln(int level) {
		if(level <= minLevel){
			pw.println();
			pw.flush();
		}
	}

	@Override
	public void writeln(Object obj, int level, int padding) {
		write(obj, level, padding);
		writeln(level);
	}

	@Override
	public void writeTitle(Object obj, int level) {
		if(level <= minLevel){
			pw.println();
			pw.println("----------" + obj + "----------");
			pw.flush();
		}
	}
	
	/**
	 * Close file
	 */
	public void close(){
		pw.close();
	}

}
