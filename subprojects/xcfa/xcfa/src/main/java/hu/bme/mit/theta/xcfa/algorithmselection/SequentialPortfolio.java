package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;

import java.time.Duration;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class SequentialPortfolio extends AbstractPortfolio {
	private CegarConfiguration[] configurations = new CegarConfiguration[3];
	private final long sumTime = 100*1000; // in ms, with initialization time
	private long analysisTime; // in ms, init time subtracted from sumTime

	public SequentialPortfolio(Logger.Level logLevel, String basicFileName, String modelName) {
		super(logLevel, basicFileName, modelName);
		configurations[0] = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.SEQ_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				false
		);
		configurations[1] = new CegarConfiguration(
				CfaConfigBuilder.Domain.PRED_CART,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				false
		);
		configurations[2] = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.NWT_IT_WP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				false
		);
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(CFA cfa, Duration initializationTime) {
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
			result = executeConfiguration(configuration, cfa, timeout);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
				logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

				return result.get2().get();
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
