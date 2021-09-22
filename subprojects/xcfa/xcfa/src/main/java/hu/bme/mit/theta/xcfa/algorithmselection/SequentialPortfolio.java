package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;

import java.sql.Time;
import java.time.Duration;
import java.time.temporal.TemporalUnit;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkState;

// TODO remove arg/cex check
public class SequentialPortfolio extends AbstractPortfolio {
	private CegarConfiguration[] configurations = new CegarConfiguration[3];
	private final long maxTimeout; // in ms, third of analysisTime
	private final long sumTime = 100*1000; // 900*1000; // in ms, with initialization time
	private final long analysisTime; // in ms, init time subtracted from sumTime

	public SequentialPortfolio(Logger.Level logLevel, Duration initializationTime) {
		super(logLevel);
		analysisTime = sumTime - initializationTime.toMillis();
		maxTimeout = analysisTime/3;
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
			} else {
				timeout = maxTimeout;
			}
			Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, timeout);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				return result.get2().get();
			}
		}
		logger.write(Logger.Level.MAINSTEP, "Sequential portfolio done");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		return null;
	}
}
