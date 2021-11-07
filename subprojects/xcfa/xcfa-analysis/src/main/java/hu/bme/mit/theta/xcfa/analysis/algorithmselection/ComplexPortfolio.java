package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.time.Duration;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class ComplexPortfolio extends AbstractPortfolio {
	private final long sumTime = 900*1000; // in ms, with initialization time
	private long analysisTime; // in ms, init time subtracted from sumTime
	private long startCpuTime;

	public ComplexPortfolio(Logger.Level logLevel, String modelName, String smtlibhome) throws Exception {
		super(logLevel, modelName, smtlibhome); // registers solver factories
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(XCFA xcfa, Duration initializationTime) throws Exception {
		logger.write(Logger.Level.MAINSTEP, "Executing complex portfolio...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		startCpuTime = CpuTimeKeeper.getCurrentCpuTime()*1000;
		analysisTime = sumTime - initializationTime.toMillis();

		SafetyResult<?, ?> safetyResult;
		if(ArchitectureConfig.arithmetic.equals(ArchitectureConfig.ArithmeticType.bitvector)) {
			logger.write(Logger.Level.SUBSTEP, "Choosing bitvector arithmetic");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			safetyResult = bitvectorPath(xcfa);
		} else {
			logger.write(Logger.Level.SUBSTEP, "Choosing integer arithmetic");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			safetyResult = integerPath(xcfa);
		}
		// TODO this will change if we start to use more solvers
		outputResultFiles(safetyResult, "verify");
		return safetyResult;
	}

	private SafetyResult<?, ?> integerPath(XCFA xcfa) throws Exception {
		ModelStatistics statistics = ModelStatistics.createXcfaStatistics(xcfa, modelName);
		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = null;

		if(statistics.getWhileLoops()>0 && statistics.getCyclomaticComplexity() <= 30) {
			result = runShortPred(xcfa);
			if(result.get1().equals(Result.SUCCESS)) {
				checkState(result.get2().isPresent());
				return result.get2().get();
			}
		}

		if(statistics.getHavocCount()<=5 && statistics.getVarCount()>10) {
			result = runAllvarsExpl(xcfa);
		} else {
			result = runEmptyExpl(xcfa);
		}
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		}

		result = runLongPred(xcfa);
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		} else if(!result.get1().equals(Result.TIMEOUT)) {
			result = runPredBool(xcfa);
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
		long remainingTime = analysisTime-(CpuTimeKeeper.getCurrentCpuTime()*1000-startCpuTime);
		return remainingTime;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runPredBool(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_BOOL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runLongPred(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_CART,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runEmptyExpl(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (5.0 / 9.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runAllvarsExpl(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.ALLVARS,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (400.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}


	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runShortPred(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_CART,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (30.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private SafetyResult<?, ?> bitvectorPath(XCFA xcfa) throws Exception {
		CegarConfiguration bitvecConf1 = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.NWT_IT_WP,
				XcfaConfigBuilder.Search.ERR,
				XcfaConfigBuilder.PredSplit.WHOLE,
				XcfaConfigBuilder.Algorithm.DECL,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"verify",
				"verify"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(bitvecConf1, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Sequential portfolio successful, solver: " + bitvecConf1);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
			return result.get2().get();
		} else if(!result.get1().equals(Result.TIMEOUT)) {
			CegarConfiguration bitvecConf2 = new CegarConfiguration(
					XcfaConfigBuilder.Domain.EXPL,
					XcfaConfigBuilder.Refinement.NWT_IT_WP,
					XcfaConfigBuilder.Search.ERR,
					XcfaConfigBuilder.PredSplit.WHOLE,
					XcfaConfigBuilder.Algorithm.DECL,
					1,
					XcfaConfigBuilder.InitPrec.EMPTY,
					PruneStrategy.FULL,
					true,
					"verify",
					"verify"
			);

			result = executeConfiguration(bitvecConf2, xcfa, calculateRemainingTime());
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
