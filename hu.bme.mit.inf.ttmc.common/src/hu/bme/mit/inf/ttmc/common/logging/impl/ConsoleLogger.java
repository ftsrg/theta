package hu.bme.mit.inf.ttmc.common.logging.impl;

import hu.bme.mit.inf.ttmc.common.logging.Logger;

public class ConsoleLogger extends MinLevelBasedLogger implements Logger {

	public ConsoleLogger(int minLevel) {
		super(minLevel);
	}

	@Override
	public void write(Object obj, int level, int padding) {
		if(level <= minLevel){
			for(int i = 0; i < padding; ++i) System.out.print("   ");
			System.out.print(obj);
		}
	}

	@Override
	public void writeln(int level) {
		if(level <= minLevel) System.out.println();		
	}

	@Override
	public void writeln(Object obj, int level, int padding) {
		write(obj, level, padding);
		writeln(level);
	}

	@Override
	public void writeHeader(Object obj, int level) {
		if(level <= minLevel){
			System.out.println();
			System.out.println("----------" + obj + "----------");
		}
	}

}
