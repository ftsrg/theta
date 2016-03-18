package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

/**
 * Base class for loggers with a minimal level
 * @author Akos
 */
public abstract class LoggerBase implements ILogger {
	protected int minLevel; // Only write below this level
	
	/**
	 * Constructor
	 * @param minLevel Write only below this level
	 */
	public LoggerBase(int minLevel){
		this.minLevel = minLevel;
	}

	@Override
	public void write(Object obj, int level) {
		write(obj, level, 0);
	}

	@Override
	public void writeln(Object obj, int level) {
		writeln(obj, level, 0);
	}

}
