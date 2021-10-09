package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.xcfa.model.XCFA;

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

	public abstract hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(XCFA xcfa, Duration initializationTime);

	/**
	 *
	 * @param configuration
	 * @param xcfa
	 * @param timeout in ms
	 * @return
	 */
	protected Tuple2<Result, Optional<SafetyResult<?,?>>> executeConfiguration(CegarConfiguration configuration, XCFA xcfa, long timeout) {
		logger.write(Logger.Level.MAINSTEP, "Executing ");
		logger.write(Logger.Level.MAINSTEP, configuration.toString());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Timeout is set to " + timeout/1000.0 + " sec (cputime)...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		long startCpuTime = CpuTimeKeeper.getCurrentCpuTime();

		com.microsoft.z3.Global.resetParameters(); // TODO not sure if this is needed or not

		CegarAnalysisThread cegarAnalysisThread = new CegarAnalysisThread(xcfa, logger, configuration);

		Stopwatch stopwatch = Stopwatch.createStarted();
		cegarAnalysisThread.start();

		try {
			if(timeout==-1) {
				synchronized (cegarAnalysisThread) {
					cegarAnalysisThread.wait();
				}
			} else {
				long startTime;
				long decreasingTimeout = timeout/1000; // in seconds!
				while(decreasingTimeout > 0 && cegarAnalysisThread.isAlive()) {
					startTime = CpuTimeKeeper.getCurrentCpuTime();
					synchronized (cegarAnalysisThread) {
						cegarAnalysisThread.wait(decreasingTimeout*1000/2, 0);
					}
					long elapsedCpuTime = CpuTimeKeeper.getCurrentCpuTime()-startTime;
					decreasingTimeout -= elapsedCpuTime;
				}
			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		if(cegarAnalysisThread.isAlive()) {
			Stopwatch dieTimer = Stopwatch.createStarted();

			try {
				SolverManager.closeAll();
			} catch (Exception e) {
				System.err.println("Could not close solver; possible resource leak");
				e.printStackTrace();
			}
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
		long cpuTimeTaken = CpuTimeKeeper.getCurrentCpuTime() - startCpuTime;

		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Execution done, result: ");
		logger.write(Logger.Level.MAINSTEP, result.toString());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, "Time taken in this configuration: ");
		logger.write(Logger.Level.MAINSTEP,  cpuTimeTaken + " sec (cputime)");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		writeCsvLine(configuration, timeout, timeTaken, cpuTimeTaken, result);
		writeTxtLine(configuration, timeout, timeTaken, cpuTimeTaken, result);
		return Tuple2.of(result, Optional.ofNullable(safetyResult));
	}

	private void writeTxtLine(CegarConfiguration configuration, long timeout, long timeTaken, long cpuTimeTaken, Result result) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(configuration);
		stringBuilder.append(", timeout (ms, cputime): ").append(timeout);
		stringBuilder.append(", walltime taken (ms): ").append(timeTaken);
		stringBuilder.append(", cputime taken (s): ").append(cpuTimeTaken);
		stringBuilder.append(", result: ").append(result);
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationTxt, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void writeCsvLine(CegarConfiguration configuration, long timeout, long timeTaken, long cpuTimeTaken, Result result) {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append(modelName).append("\t");
		stringBuilder.append(configuration).append("\t");
		stringBuilder.append(timeout).append("\t");
		stringBuilder.append(timeTaken).append("\t");
		stringBuilder.append(cpuTimeTaken).append("\t");
		stringBuilder.append(result).append("\t");
		stringBuilder.append(System.lineSeparator());

		try (BufferedWriter bw = new BufferedWriter(new FileWriter(configurationCsv, true))) {
			bw.write(stringBuilder.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
