package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.File;
import java.time.Duration;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkState;

public class SequentialPortfolio extends AbstractPortfolio {
	private CegarConfiguration[] configurations = new CegarConfiguration[3];
	private final long sumTime = 900*1000; // in ms, with initialization time
	private final long analysisTime; // in ms, init time subtracted from sumTime

	public SequentialPortfolio(Logger.Level logLevel, Duration initializationTime, String basicFileName, String modelName) {
		super(logLevel, basicFileName, modelName);
		analysisTime = sumTime - initializationTime.toMillis();
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
	public SafetyResult<?, ?> executeAnalysis(CFA cfa) {
		logger.write(Logger.Level.MAINSTEP, "Executing sequential portfolio...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		Stopwatch stopwatch = Stopwatch.createStarted();

		for (int i = 0; i < configurations.length; i++) {
			CegarConfiguration configuration = configurations[i];
			long remainingTime = analysisTime-stopwatch.elapsed(TimeUnit.MILLISECONDS);
			long timeout;
			if(i==2) {
				timeout = remainingTime;
			} else if(i==1) {
				timeout = remainingTime/2;
			} else {
				timeout = remainingTime/3;
			}
			Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, timeout);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
				logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

				return result.get2().get();
			}
		}
		logger.write(Logger.Level.MAINSTEP, "Sequential portfolio was unsuccessful");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		return null;
	}
}
