package hu.bme.mit.theta.xcfa.analysis.portfolio.common;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.model.XCFA;

/**
 * the "analysis thread" for portfolios - {@link AbstractPortfolio} uses this thread class
 * to call and manage the analysis (the steps in the portfolio)
 * (e.g. handling/issuing timeouts)
 */
class CegarAnalysisThread extends Thread {
	private final XCFA xcfa;
	private final CegarConfiguration configuration;
	private final ConsoleLogger logger;
	private final XcfaConfig<?, ?, ?> xcfaConfig;

	private volatile Result result = Result.UNKNOWN;
	private volatile SafetyResult<?, ?> safetyResult;

	CegarAnalysisThread(XCFA xcfa, ConsoleLogger logger, CegarConfiguration configuration) throws Exception {
		this.xcfa = xcfa;
		this.logger = logger;
		this.configuration = configuration;
		this.safetyResult = null;
		xcfaConfig = configuration.buildConfiguration(xcfa, logger);
	}

	public Result getResult() {
		return result;
	}

	public SafetyResult<?, ?> getSafetyResult() {
		return safetyResult;
	}

	/**
	 * Executes the given analysis on this thread and saves the result in volatile member variables
	 * Catches and handles different exceptions regarding the result
	 * (not solvable, solver exception, out of memory error, generic exceptions, i.e. unknown result)
	 */
	@Override
	public void run() {
		try {
			try {
				safetyResult = xcfaConfig.check();

				if(safetyResult.isUnsafe() || safetyResult.isSafe()) {
					result = Result.SUCCESS;
				} else {
					result = Result.UNKNOWN;
				}
			} catch (NotSolvableException nse) {
				safetyResult = null;
				result = Result.STUCK;
			} catch (UnknownSolverStatusException | SmtLibSolverException s) {
				safetyResult = null;
				result = Result.SOLVERISSUE;
				s.printStackTrace();
			} catch (Exception e) {
				safetyResult = null;
				result = Result.UNKNOWN;
				e.printStackTrace();
			}
		} catch (OutOfMemoryError E) {
			System.err.println(System.lineSeparator());
			System.err.println("Used memory before gc: " + (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()));
			System.gc();
			result = Result.OUTOFMEMORY;
			safetyResult = null;
			System.err.println("Used memory after gc: " + (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()));
		}
	}

	/**
	 * Has to be called explicitly to set the results to timeout after the thread itself is dead
	 */
	public void timeout() {
		result = Result.TIMEOUT;
		safetyResult = null;
	}
}
