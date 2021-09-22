package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;

import java.util.concurrent.Future;

import static com.google.common.base.Preconditions.checkState;

class CegarAnalysisThread extends Thread {
	private final CFA cfa;
	private final CegarConfiguration configuration;
	private final ConsoleLogger logger;

	private volatile Result result = Result.UNKNOWN;
	private volatile SafetyResult<?, ?> safetyResult;

	CegarAnalysisThread(CFA cfa, ConsoleLogger logger, CegarConfiguration configuration) {
		this.cfa = cfa;
		this.logger = logger;
		this.configuration = configuration;
		this.safetyResult = null;
	}

	public Result getResult() {
		return result;
	}

	public SafetyResult<?, ?> getSafetyResult() {
		return safetyResult;
	}

	@Override
	public void run() {
		checkState(cfa.getErrorLoc().isPresent());
		try {
			safetyResult = configuration.buildConfiguration(cfa, cfa.getErrorLoc().get(), logger).check();

			if(safetyResult.isUnsafe() || safetyResult.isSafe()) {
				result = Result.SUCCESS;
			} else {
				result = Result.UNKNOWN;
			}
		} catch (NotSolvableException nse) {
			safetyResult = null;
			result = Result.STUCK;
		} catch (Exception e) {
			safetyResult = null;
			result = Result.UNKNOWN;
			e.printStackTrace();
		}
	}

	public void timeout() {
		result = Result.TIMEOUT;
		safetyResult = null;
	}
}
