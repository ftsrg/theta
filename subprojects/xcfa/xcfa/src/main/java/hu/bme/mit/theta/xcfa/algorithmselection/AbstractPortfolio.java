package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3.ContextInterrupt;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.Duration;
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
	private final File configurationTxt;
	private final File configurationCsv;
	protected final String modelName;

	public AbstractPortfolio(Logger.Level logLevel, String basicFileName, String modelName) {
		logger = new ConsoleLogger(logLevel);
		configurationTxt = new File(basicFileName + ".portfolio.txt");
		configurationCsv = new File(basicFileName + ".portfolio.csv");
		this.modelName = modelName;
	}

	public abstract hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(CFA cfa, Duration initializationTime);

	/**
	 *
	 * @param configuration
	 * @param cfa
	 * @param timeout in ms
	 * @return
	 */
	protected Tuple2<Result, Optional<SafetyResult<?,?>>> executeConfiguration(CegarConfiguration configuration, CFA cfa, long timeout) {
		logger.write(Logger.Level.MAINSTEP, "Executing ");
		logger.write(Logger.Level.MAINSTEP, configuration.toString());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Timeout is set to " + timeout/1000.0 + " sec (cputime)...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		long earlierGcTime = GcTimer.getGcTime();

		com.microsoft.z3.Global.resetParameters(); // TODO not sure if this is needed or not

		CegarAnalysisThread cegarAnalysisThread = new CegarAnalysisThread(cfa, logger, configuration);

		Stopwatch stopwatch = Stopwatch.createStarted();
		cegarAnalysisThread.start();

		try {
			if(timeout==-1) {
				synchronized (cegarAnalysisThread) {
					cegarAnalysisThread.wait();
				}
			} else {
				long pastGcTime = GcTimer.getGcTime();
				long gcTime;
				Stopwatch stopwatch1;
				while(timeout>5 && cegarAnalysisThread.isAlive()) {
					stopwatch1 = Stopwatch.createStarted();
					synchronized (cegarAnalysisThread) {
						cegarAnalysisThread.wait(timeout/2, 0);
					}
					gcTime = GcTimer.getGcTime();
					long newGcTime = gcTime-pastGcTime;
					timeout = timeout-stopwatch1.elapsed(TimeUnit.MILLISECONDS)-newGcTime;
					pastGcTime = gcTime;
				}
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		if(cegarAnalysisThread.isAlive()) {
			Stopwatch dieTimer = Stopwatch.createStarted();

			ContextInterrupt.interruptContexts();
			cegarAnalysisThread.stop(); // Not a good idea, but no better option

			synchronized (cegarAnalysisThread) {
				try {
					cegarAnalysisThread.wait();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
			System.err.println("Timeouting thread dead after " + dieTimer.elapsed(TimeUnit.MILLISECONDS) + "ms");

			cegarAnalysisThread.timeout(); // set the result to TIMEOUT and null
			dieTimer.stop();
		}

		stopwatch.stop();

		Result result = cegarAnalysisThread.getResult();
		SafetyResult<?, ?> safetyResult = cegarAnalysisThread.getSafetyResult();

		long timeTaken = stopwatch.elapsed(TimeUnit.MILLISECONDS);

		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Execution done, result: ");
		logger.write(Logger.Level.MAINSTEP, result.toString());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Time taken in this configuration: ");
		logger.write(Logger.Level.MAINSTEP, (timeTaken+(GcTimer.getGcTime()-earlierGcTime))/1000.0 + " sec (cputime)");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		writeCsvLine(configuration, timeout, timeTaken, result);
		writeTxtLine(configuration, timeout, timeTaken, result);
		return Tuple2.of(result, Optional.ofNullable(safetyResult));
	}

	private void writeTxtLine(CegarConfiguration configuration, long timeout, long timeTaken, Result result) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(configuration);
		stringBuilder.append(", timeout (ms): ").append(timeout);
		stringBuilder.append(", time taken (ms): ").append(timeTaken);
		stringBuilder.append(", result: ").append(result);
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationTxt, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void writeCsvLine(CegarConfiguration configuration, long timeout, long timeTaken, Result result) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(modelName).append("\t");
		stringBuilder.append(configuration).append("\t");
		stringBuilder.append(timeout).append("\t");
		stringBuilder.append(timeTaken).append("\t");
		stringBuilder.append(result).append("\t");
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationCsv, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
