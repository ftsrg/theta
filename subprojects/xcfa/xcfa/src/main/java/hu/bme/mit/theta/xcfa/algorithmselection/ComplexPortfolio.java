package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.File;
import java.time.Duration;

import static com.google.common.base.Preconditions.checkState;

public class ComplexPortfolio extends AbstractPortfolio {
	private final long sumTime = 900*1000; // 900*1000; // in ms, with initialization time
	private final long analysisTime; // in ms, init time subtracted from sumTime

	public ComplexPortfolio(Logger.Level logLevel, Duration initializationTime, String basicFileName, String modelName) {
		super(logLevel, basicFileName, modelName);
		analysisTime = sumTime - initializationTime.toMillis();

	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(CFA cfa) {
		return null;
	}
}
