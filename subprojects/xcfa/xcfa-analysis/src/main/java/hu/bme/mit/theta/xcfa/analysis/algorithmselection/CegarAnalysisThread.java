package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.solver.UnknownSolverStatusException;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfig;
import hu.bme.mit.theta.xcfa.model.XCFA;

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

	public void timeout() {
		result = Result.TIMEOUT;
		safetyResult = null;
	}
}
