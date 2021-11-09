package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.time.Duration;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class SequentialPortfolio extends AbstractPortfolio {
	private CegarConfiguration[] configurations = new CegarConfiguration[3];
	private final long sumTime = 900*1000; // in ms, with initialization time
	private long analysisTime; // in ms, init time subtracted from sumTime

	public SequentialPortfolio(Logger.Level logLevel, String modelName, String smtlibhome) throws Exception {
		super(logLevel, modelName, smtlibhome); // registers solver factories

		configurations[0] = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.SINGLETHREAD,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				false,
				"Z3", "Z3"
		);
		configurations[1] = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_CART,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.SINGLETHREAD,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				false,
				"Z3", "Z3"
		);
		configurations[2] = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.NWT_IT_WP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.SINGLETHREAD,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				false,
				"Z3", "Z3"
		);
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(XCFA xcfa, Duration initializationTime) throws Exception {
		logger.write(Logger.Level.MAINSTEP, "Executing sequential portfolio...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		long startCpuTime = CpuTimeKeeper.getCurrentCpuTime()*1000;
		analysisTime = sumTime - initializationTime.toMillis();

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = null;
		for (int i = 0; i < configurations.length; i++) {
			CegarConfiguration configuration = configurations[i];

			long remainingTime = analysisTime-(CpuTimeKeeper.getCurrentCpuTime()*1000-startCpuTime);

			long timeout;
			if(i==2) {
				timeout = remainingTime;
			} else if(i==1) {
				timeout = remainingTime/2;
			} else {
				timeout = remainingTime/3;
			}
			result = executeConfiguration(configuration, xcfa, timeout);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
				logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

				SafetyResult<?, ?> safetyResult = result.get2().get();
				outputResultFiles(safetyResult, "Z3");
				return safetyResult;
			}
		}
		logger.write(Logger.Level.MAINSTEP, "Sequential portfolio was unsuccessful");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		checkState(result!=null);
		if(result.get1().equals(Result.TIMEOUT)) {
			throw new PortfolioTimeoutException("Sequential portfolio timed out");
		}

		return null;
	}
}
