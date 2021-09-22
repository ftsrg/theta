package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.Console;
import java.io.File;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

/**
 * Base class of portfolio classes
 * executeAnalysis() is already implemented and can/should be used by subclasses
 * Uses 2 threads when executing analysis
 * Uses thread.stop() if analysis times out - use at your own risk
 */
public abstract class AbstractPortfolio {
	protected final ConsoleLogger logger;

	public AbstractPortfolio(Logger.Level logLevel) {
		logger = new ConsoleLogger(logLevel);
	}

	public abstract hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(CFA cfa);

	/**
	 *
	 * @param configuration
	 * @param cfa
	 * @param timeout in ms
	 * @return
	 */
	protected Tuple2<Result, Optional<SafetyResult<?,?>>> executeConfiguration(CegarConfiguration configuration, CFA cfa, long timeout) {
		logger.write(Logger.Level.SUBSTEP, "Executing ");
		logger.write(Logger.Level.SUBSTEP, configuration.toString());
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
		logger.write(Logger.Level.SUBSTEP, "Timeout is set to " + timeout/1000.0 + " sec...");
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());

		CegarAnalysisThread cegarAnalysisThread = new CegarAnalysisThread(cfa, logger, configuration);

		cegarAnalysisThread.start();

		Stopwatch stopwatch = Stopwatch.createStarted();

		try {
			synchronized (cegarAnalysisThread) {
				cegarAnalysisThread.wait(timeout, 0);
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if(cegarAnalysisThread.isAlive()) {
			cegarAnalysisThread.stop(); // Not a good idea, but no better option
			cegarAnalysisThread.timeout(); // set the result to TIMEOUT and null
		}

		stopwatch.stop();

		Result result = cegarAnalysisThread.getResult();
		SafetyResult<?, ?> safetyResult = cegarAnalysisThread.getSafetyResult();

		logger.write(Logger.Level.SUBSTEP, "Execution done, result: ");
		logger.write(Logger.Level.SUBSTEP, result.toString());
		logger.write(Logger.Level.INFO, System.lineSeparator());
		logger.write(Logger.Level.INFO, "Time taken in this configuration: ");
		logger.write(Logger.Level.INFO, stopwatch.elapsed(TimeUnit.MILLISECONDS) / 1000.0 + " sec");
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
		logger.write(Logger.Level.INFO, "Result is: ");
		logger.write(Logger.Level.INFO, result.toString());
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
		logger.write(Logger.Level.SUBSTEP, System.lineSeparator());

		return Tuple2.of(result, Optional.ofNullable(safetyResult));
	}
}
