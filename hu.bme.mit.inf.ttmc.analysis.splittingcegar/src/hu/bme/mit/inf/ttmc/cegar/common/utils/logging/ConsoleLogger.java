package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

/**
 * Console logger
 * @author Akos
 */
public class ConsoleLogger extends LoggerBase {
	/**
	 * Constructor
	 * @param minLevel Write only below this level
	 */
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
	public void writeTitle(Object obj, int level) {
		if(level <= minLevel){
			System.out.println();
			System.out.println("----------" + obj + "----------");
		}
	}

}
