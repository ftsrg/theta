package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Composite logger, logs to other loggers
 * @author Akos
 *
 */
public class CompositeLogger implements ILogger {
	private List<ILogger> loggers; // List of loggers
	
	/**
	 * Constructor
	 * @param loggers Array of loggers
	 */
	public CompositeLogger(ILogger[] loggers){
		this.loggers = new ArrayList<ILogger>(loggers.length);
		for(int i=0;i<loggers.length;++i) this.loggers.add(loggers[i]);
	}
	
	/**
	 * Constructor
	 * @param loggers Collection of loggers
	 */
	public CompositeLogger(Collection<ILogger> loggers){
		this.loggers = new ArrayList<ILogger>(loggers);
	}
	
	@Override
	public void write(Object obj, int level) {
		for(ILogger logger : loggers) logger.write(obj, level);
	}

	@Override
	public void write(Object obj, int level, int padding) {
		for(ILogger logger : loggers) logger.write(obj, level, padding);
	}

	@Override
	public void writeln(int level) {
		for(ILogger logger : loggers) logger.writeln(level);
	}

	@Override
	public void writeln(Object obj, int level) {
		for(ILogger logger : loggers) logger.writeln(obj, level);
	}

	@Override
	public void writeln(Object obj, int level, int padding) {
		for(ILogger logger : loggers) logger.writeln(obj, level, padding);
	}

	@Override
	public void writeTitle(Object obj, int level) {
		for(ILogger logger : loggers) logger.writeTitle(obj, level);
	}

}
