package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xcfa.analysis.utils.OutputHandler;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.nio.file.Path;
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
	protected final String modelName;
	protected final String smtlibHome;

	public AbstractPortfolio(Logger.Level logLevel, String modelName, String smtlibHome) throws Exception {
		logger = new ConsoleLogger(logLevel);
		closeAndRegisterAllSolverManagers(smtlibHome, logger);
		this.modelName = modelName;
		this.smtlibHome = smtlibHome;
	}

	public abstract hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(XCFA xcfa, Duration initializationTime) throws Exception;

	public void outputResultFiles(SafetyResult<?, ?> status, String refinementSolver) throws Exception {
		if (status!=null && status.isUnsafe()) {
			OutputHandler.getInstance().writeCounterexamples(status, refinementSolver);
		} else if(status!=null && status.isSafe()) {
			OutputHandler.getInstance().writeDummyCorrectnessWitness();
		}
	}

	/**
	 *
	 * @param configuration
	 * @param xcfa
	 * @param timeout in ms
	 * @return
	 */
	protected Tuple2<Result, Optional<SafetyResult<?,?>>> executeConfiguration(CegarConfiguration configuration, XCFA xcfa, long timeout) {
		logger.write(Logger.Level.RESULT, "Executing ");
		logger.write(Logger.Level.RESULT, configuration.toString());
		logger.write(Logger.Level.RESULT, System.lineSeparator());
		logger.write(Logger.Level.RESULT, "Timeout is set to " + timeout/1000.0 + " sec (cputime)...");
		logger.write(Logger.Level.RESULT, System.lineSeparator());
		logger.write(Logger.Level.RESULT, System.lineSeparator());

		long startCpuTime = CpuTimeKeeper.getCurrentCpuTime();

		com.microsoft.z3.Global.resetParameters(); // TODO not sure if this is needed or not

		CegarAnalysisThread cegarAnalysisThread;
		try {
			cegarAnalysisThread = new CegarAnalysisThread(xcfa, logger, configuration);
		} catch (Exception e) {
			e.printStackTrace();
			return Tuple2.of(Result.UNKNOWN, Optional.empty());
		}

		Stopwatch stopwatch = Stopwatch.createStarted();
		cegarAnalysisThread.setName("analysis-worker");
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
			cegarAnalysisThread.interrupt();
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			cegarAnalysisThread.stop(); // Not a good idea, but no better option

			try {
				closeAllSolverManagers();
			} catch (Exception e) {
				System.err.println("Could not close solver; possible resource leak");
				e.printStackTrace();
			}
			cegarAnalysisThread.interrupt();
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			cegarAnalysisThread.stop(); // Not a good idea, but no better option

			synchronized (cegarAnalysisThread) {
				while(cegarAnalysisThread.isAlive()) {
					try {
						cegarAnalysisThread.wait(1000, 0);
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
			}
			System.err.println("Timeouting thread dead after " + dieTimer.elapsed(TimeUnit.MILLISECONDS) + "ms");

			cegarAnalysisThread.timeout(); // set the result to TIMEOUT and null
			dieTimer.stop();
			try {
				registerAllSolverManagers(smtlibHome, logger);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		stopwatch.stop();

		Result result = cegarAnalysisThread.getResult();
		SafetyResult<?, ?> safetyResult = cegarAnalysisThread.getSafetyResult();

		long timeTaken = stopwatch.elapsed(TimeUnit.MILLISECONDS);
		long cpuTimeTaken = CpuTimeKeeper.getCurrentCpuTime() - startCpuTime;

		logger.write(Logger.Level.RESULT, System.lineSeparator());
		logger.write(Logger.Level.RESULT, "Execution done, result: ");
		logger.write(Logger.Level.RESULT, result.toString());
		logger.write(Logger.Level.RESULT, System.lineSeparator());
		logger.write(Logger.Level.RESULT, "Time taken in this configuration: ");
		logger.write(Logger.Level.RESULT,  cpuTimeTaken + " sec (cputime)");
		logger.write(Logger.Level.RESULT, System.lineSeparator());
		logger.write(Logger.Level.RESULT, System.lineSeparator());

		OutputHandler.getInstance().writeCsvLine(configuration, timeout, timeTaken, cpuTimeTaken, result);
		OutputHandler.getInstance().writeTxtLine(configuration, timeout, timeTaken, cpuTimeTaken, result);
		try {
			closeAndRegisterAllSolverManagers(smtlibHome, logger);
		} catch (Exception e) {
			System.err.println("Could not close solver; possible resource leak");
			e.printStackTrace();
		}
		return Tuple2.of(result, Optional.ofNullable(safetyResult));
	}

	private static void closeAndRegisterAllSolverManagers(String home, Logger logger) throws Exception {
		CpuTimeKeeper.saveSolverTimes();
		SolverManager.closeAll();
		// register solver managers
		SolverManager.registerSolverManager(Z3SolverManager.create());
		if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
			final var homePath = Path.of(home);
			final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
			SolverManager.registerSolverManager(smtLibSolverManager);
		}
	}

	private static void closeAllSolverManagers() throws Exception {
		CpuTimeKeeper.saveSolverTimes();
		SolverManager.closeAll();
	}


	private static void registerAllSolverManagers(String home, Logger logger) throws Exception {
		SolverManager.registerSolverManager(Z3SolverManager.create());
		if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
			final var homePath = Path.of(home);
			final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);
			SolverManager.registerSolverManager(smtLibSolverManager);
		}
	}
}
