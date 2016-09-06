package hu.bme.mit.inf.theta.common.logging.impl;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

import hu.bme.mit.inf.theta.common.logging.Logger;

public final class FileLogger extends MinLevelBasedLogger implements Logger {
	private final PrintWriter pw;
	private boolean instantFlush;

	public FileLogger(int minLevel, String fileName, boolean instantFlush) throws FileNotFoundException {
		super(minLevel);
		pw = new PrintWriter(fileName);
		this.instantFlush = instantFlush;
	}

	@Override
	public void write(Object obj, int level, int padding) {
		if(level <= minLevel){
			for(int i = 0; i < padding; ++i) pw.print("   ");
			pw.print(obj);
			if (instantFlush) pw.flush();
		}
	}

	@Override
	public void writeln(int level) {
		if(level <= minLevel){
			pw.println();
			if (instantFlush) pw.flush();
		}
	}

	@Override
	public void writeln(Object obj, int level, int padding) {
		write(obj, level, padding);
		writeln(level);
	}

	@Override
	public void writeHeader(Object obj, int level) {
		if(level <= minLevel){
			pw.println();
			pw.println("----------" + obj + "----------");
			if (instantFlush) pw.flush();
		}
	}

	public void close(){
		pw.close();
	}

}
