package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;

import java.io.File;
import java.time.Duration;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkState;

public class ComplexPortfolio extends AbstractPortfolio {
	private final long sumTime = 900*1000; // in ms, with initialization time
	private long analysisTime; // in ms, init time subtracted from sumTime
	private long gcTime = 0;
	private Stopwatch stopwatch = null;

	public ComplexPortfolio(Logger.Level logLevel, String basicFileName, String modelName) {
		super(logLevel, basicFileName, modelName);
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(CFA cfa, Duration initializationTime) {
		logger.write(Logger.Level.MAINSTEP, "Executing complex portfolio...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		gcTime = GcTimer.getGcTime();
		analysisTime = sumTime - initializationTime.toMillis() - gcTime;
		stopwatch = Stopwatch.createStarted();

		if(ArchitectureConfig.arithmetic.equals(ArchitectureConfig.ArithmeticType.bitvector)) {
			logger.write(Logger.Level.SUBSTEP, "Choosing bitvector arithmetic");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			return bitvectorPath(cfa);
		} else {
			logger.write(Logger.Level.SUBSTEP, "Choosing integer arithmetic");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			return integerPath(cfa);
		}
	}

	private SafetyResult<?, ?> integerPath(CFA cfa) {
		ModelStatistics statistics = ModelStatistics.createCfaStatistics(cfa, modelName);
		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = null;

		if(statistics.getWhileLoops()>0 && statistics.getCyclomaticComplexity() <= 30) {
			result = runShortPred(cfa);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				return result.get2().get();
			}
		}

		if(statistics.getHavocCount()<=5 && statistics.getVarCount()>10) {
			result = runAllvarsExpl(cfa);
		} else {
			result = runEmptyExpl(cfa);
		}
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		}

		result = runLongPred(cfa);
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		} else if(!result.get1().equals(Result.TIMEOUT)) {
			result = runPredBool(cfa);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				return result.get2().get();
			} else {
				return null; // unsuccessful, but not a timeout
			}
		} else { // long pred timed out
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
	}

	private long calculateRemainingTime() {
		long newGcTime = GcTimer.getGcTime();
		long remainingTime = analysisTime-stopwatch.elapsed(TimeUnit.MILLISECONDS)-(newGcTime-gcTime);
		gcTime = newGcTime;
		return remainingTime;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runPredBool(CFA cfa) {
		CegarConfiguration configuration = new CegarConfiguration(
				CfaConfigBuilder.Domain.PRED_BOOL,
				CfaConfigBuilder.Refinement.SEQ_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runLongPred(CFA cfa) {
		CegarConfiguration configuration = new CegarConfiguration(
				CfaConfigBuilder.Domain.PRED_CART,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runEmptyExpl(CFA cfa) {
		CegarConfiguration configuration = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.SEQ_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, (long) (5.0 / 9.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runAllvarsExpl(CFA cfa) {
		CegarConfiguration configuration = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.SEQ_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.ALLVARS,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, (long) (400.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}


	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runShortPred(CFA cfa) {
		CegarConfiguration configuration = new CegarConfiguration(
				CfaConfigBuilder.Domain.PRED_CART,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, cfa, (long) (30.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private SafetyResult<?, ?> bitvectorPath(CFA cfa) {
		CegarConfiguration bitvecConf1 = new CegarConfiguration(
				CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.NWT_IT_WP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				CfaConfigBuilder.Encoding.LBE,
				true
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(bitvecConf1, cfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + bitvecConf1);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
			return result.get2().get();
		} else if(!result.get1().equals(Result.TIMEOUT)) {
			CegarConfiguration bitvecConf2 = new CegarConfiguration(
					CfaConfigBuilder.Domain.EXPL,
					CfaConfigBuilder.Refinement.NWT_IT_WP,
					CfaConfigBuilder.PrecGranularity.GLOBAL,
					CfaConfigBuilder.Search.ERR,
					CfaConfigBuilder.PredSplit.WHOLE,
					1,
					CfaConfigBuilder.InitPrec.EMPTY,
					PruneStrategy.FULL,
					CfaConfigBuilder.Encoding.LBE,
					true
			);

			result = executeConfiguration(bitvecConf2, cfa, calculateRemainingTime());
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + bitvecConf2);
				logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
				return result.get2().get();
			} else if(result.get1().equals(Result.TIMEOUT)) {
				throw new PortfolioTimeoutException("Complex portfolio timed out");
			} else {
				return null; // TODO maybe try another config here
			}
		} else {
			return null; // first nwt timed out
		}
	}


}
