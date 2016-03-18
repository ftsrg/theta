package hu.bme.mit.inf.ttmc.cegar.common.utils.logging;

/**
 * Interface for loggers
 * @author Akos
 */
public interface ILogger {
	/**
	 * Write an object
	 * @param obj Object
	 * @param level Level
	 */
	void write(Object obj, int level);
	
	/**
	 * Write an object with padding
	 * @param obj Object
	 * @param level Level
	 * @param padding Padding
	 */
	void write(Object obj, int level, int padding);
	
	/**
	 * Write a line break
	 * @param level Level
	 */
	void writeln(int level);
	
	/**
	 * Write an object with line break
	 * @param obj Object
	 * @param level Level
	 */
	void writeln(Object obj, int level);

	/**
	 * Write an object with padding and line break
	 * @param obj Object
	 * @param level Level
	 * @param padding Padding
	 */
	void writeln(Object obj, int level, int padding);
	
	/**
	 * Write as title
	 * @param obj Object
	 * @param level Level
	 */
	void writeTitle(Object obj, int level);
}
