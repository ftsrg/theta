package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.Console;
import java.io.File;
import java.util.Optional;

// TODO log what's happening
/**
 * Base class of portfolio classes
 * executeAnalysis() is already implemented and can/should be used by subclasses
 * Uses 2 threads when executing analysis
 * Uses thread.stop() if analysis times out - use at your own risk
 */
public abstract class AbstractPortfolio {
	private final ConsoleLogger logger;
	private final File statisticsFile;

	public AbstractPortfolio(Logger.Level logLevel, File statistics) {
		logger = new ConsoleLogger(logLevel);
		this.statisticsFile = statistics;
	}

	public abstract hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(CFA cfa);

	protected Tuple2<Result, Optional<SafetyResult<?,?>>> executeConfiguration(CegarConfiguration configuration, CFA cfa, long timeout) {
		logger.write(Logger.Level.INFO, "Executing configuration: ");
		logger.write(Logger.Level.INFO, configuration.toString());
		logger.write(Logger.Level.INFO, System.lineSeparator());
		logger.write(Logger.Level.INFO, "Timeout: " + timeout);
		logger.write(Logger.Level.INFO, System.lineSeparator());

		CegarAnalysisThread cegarAnalysisThread = new CegarAnalysisThread(cfa, logger, configuration);

		cegarAnalysisThread.start();

		try {
			synchronized (cegarAnalysisThread) {
				cegarAnalysisThread.wait(timeout * 1000, 0);
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if(cegarAnalysisThread.isAlive()) {
			cegarAnalysisThread.stop(); // Not a good idea, but no better option
			cegarAnalysisThread.timeout(); // set the result to TIMEOUT and null
		}

		Result result = cegarAnalysisThread.getResult();
		SafetyResult<?, ?> safetyResult = cegarAnalysisThread.getSafetyResult();

		logger.write(Logger.Level.INFO, "Execution done, result: ");
		logger.write(Logger.Level.INFO, result.toString());
		logger.write(Logger.Level.INFO, System.lineSeparator());

		return Tuple2.of(result, Optional.ofNullable(safetyResult));
	}
}
