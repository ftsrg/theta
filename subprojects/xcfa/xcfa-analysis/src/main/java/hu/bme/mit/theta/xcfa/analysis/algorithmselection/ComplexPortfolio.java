package hu.bme.mit.theta.xcfa.analysis.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseOption;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaConfigBuilder;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.time.Duration;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class ComplexPortfolio extends AbstractPortfolio {
	private final long sumTime = 900*1000; // in ms, with initialization time
	private long analysisTime; // in ms, init time subtracted from sumTime
	private long startCpuTime;

	// multithreaded parameters
	private XcfaConfigBuilder.Search search = null;
	private XcfaConfigBuilder.Algorithm algorithm = null;

	public ComplexPortfolio(Logger.Level logLevel, String modelName, String smtlibhome) throws Exception {
		super(logLevel, modelName, smtlibhome); // registers solver factories
		if(ArchitectureConfig.multiThreading) {
			algorithm = XcfaConfigBuilder.Algorithm.INTERLEAVINGS;
			search = XcfaConfigBuilder.Search.BFS;
		} else {
			algorithm = XcfaConfigBuilder.Algorithm.SINGLETHREAD;
			search = XcfaConfigBuilder.Search.ERR;
		}
	}

	@Override
	public SafetyResult<?, ?> executeAnalysis(XCFA xcfa, Duration initializationTime) throws Exception {
		logger.write(Logger.Level.MAINSTEP, "Executing complex portfolio...");
		logger.write(Logger.Level.MAINSTEP, System.lineSeparator());

		startCpuTime = CpuTimeKeeper.getCurrentCpuTime()*1000;
		analysisTime = sumTime - initializationTime.toMillis();

		SafetyResult<?, ?> safetyResult;

		BitwiseOption bitwiseOption = BitwiseChecker.getBitwiseOption();
		checkState(bitwiseOption!=null);
		if(bitwiseOption == BitwiseOption.BITWISE) {
			logger.write(Logger.Level.SUBSTEP, "Choosing bitvector arithmetic without floats");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			safetyResult = bvOnlyPath(xcfa);
			outputResultFiles(safetyResult, "mathsat:5.6.6");
		} else if(bitwiseOption == BitwiseOption.BITWISE_FLOAT) {
			logger.write(Logger.Level.SUBSTEP, "Choosing bitvector arithmetic with floats");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			safetyResult = fpbvPath(xcfa);
			outputResultFiles(safetyResult, "mathsat:fp");
		} else {
			logger.write(Logger.Level.SUBSTEP, "Choosing integer arithmetic");
			logger.write(Logger.Level.SUBSTEP, System.lineSeparator());
			safetyResult = integerPath(xcfa);
			outputResultFiles(safetyResult, "Z3");
		}
		return safetyResult;
	}

	////////// BITVECTOR (with or without bv) PATHS //////////

	private SafetyResult<?, ?> fpbvPath(XCFA xcfa) throws Exception {
		Tuple2<Result, Optional<SafetyResult<?, ?>>> result;
		result = executeExplNwtBitvectorConfig("mathsat:fp", true, xcfa);
		if(result.get1().equals(Result.SUCCESS)) {
			return result.get2().get();
		} else if(result.get1().equals(Result.SOLVERISSUE)) {
			result = executeExplNwtBitvectorConfig("cvc4:exp", false, xcfa);
			if(!result.get1().equals(Result.SUCCESS)) {
				result = executePredNwtBitvectorConfig("cvc4:exp", false, xcfa);
			}
		} else {
			result = executePredNwtBitvectorConfig("mathsat:fp", true, xcfa);
			if(!result.get1().equals(Result.SUCCESS)) {
				result = executeExplNwtBitvectorConfig("cvc4:exp", false, xcfa);
				if(!result.get1().equals(Result.SUCCESS)) {
					result = executePredNwtBitvectorConfig("cvc4:exp", false, xcfa);
				}
			}
		}

		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		} else {
			return null;
		}
	}

	private SafetyResult<?, ?> bvOnlyPath(XCFA xcfa) throws Exception {
		Tuple2<Result, Optional<SafetyResult<?, ?>>> result;
		result = executeExplSeqBitvectorConfig("mathsat:5.6.6", false, xcfa);
		if(result.get1().equals(Result.SUCCESS)) {
			return result.get2().get();
		} else if(result.get1().equals(Result.SOLVERISSUE)) {
			result = executeExplNwtBitvectorConfig("Z3", false, xcfa);
			if(!result.get1().equals(Result.SUCCESS)) {
				result = executePredNwtBitvectorConfig("Z3", false, xcfa);
			}
		} else {
			result = executePredBwBitvectorConfig("mathsat:5.6.6", false, xcfa);
			if(!result.get1().equals(Result.SUCCESS)) {
				result = executeExplNwtBitvectorConfig("Z3", false, xcfa);
				if (!result.get1().equals(Result.SUCCESS)) {
					result = executePredNwtBitvectorConfig("Z3", false, xcfa);
				}
			}
		}

		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			return result.get2().get();
		} else {
			return null;
		}
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> executeExplSeqBitvectorConfig(String solver, boolean verify, XCFA xcfa) throws Exception {
		CegarConfiguration explConfiguration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				solver,
				solver,
				verify
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(explConfiguration, xcfa, (long) (1.0/3.0*calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + explConfiguration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		} else if(result.get1().equals(Result.TIMEOUT)) {
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> executeExplNwtBitvectorConfig(String solver, boolean verify, XCFA xcfa) throws Exception {
		CegarConfiguration explConfiguration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.NWT_IT_WP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				solver,
				solver,
				verify
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(explConfiguration, xcfa, (long) (1.0/3.0*calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + explConfiguration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		} else if(result.get1().equals(Result.TIMEOUT)) {
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> executePredBwBitvectorConfig(String solver, boolean verify, XCFA xcfa) throws Exception {
		CegarConfiguration explConfiguration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				solver,
				solver,
				verify
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(explConfiguration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + explConfiguration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		} else if(result.get1().equals(Result.TIMEOUT)) {
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> executePredNwtBitvectorConfig(String solver, boolean verify, XCFA xcfa) throws Exception {
		CegarConfiguration explConfiguration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.NWT_IT_WP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				solver,
				solver,
				verify
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(explConfiguration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + explConfiguration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		} else if(result.get1().equals(Result.TIMEOUT)) {
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
		return result;
	}

	////////// INTEGER PATH //////////

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


	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runPredBool(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_BOOL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"Z3",
				"Z3"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runLongPred(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_CART,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"Z3",
				"Z3"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, calculateRemainingTime());
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runEmptyExpl(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"Z3",
				"Z3"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (5.0 / 9.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runAllvarsExpl(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.EXPL,
				XcfaConfigBuilder.Refinement.SEQ_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.ALLVARS,
				PruneStrategy.LAZY,
				true,
				"Z3",
				"Z3"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (400.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	private Tuple2<Result, Optional<SafetyResult<?, ?>>> runShortPred(XCFA xcfa) throws Exception {
		CegarConfiguration configuration = new CegarConfiguration(
				XcfaConfigBuilder.Domain.PRED_CART,
				XcfaConfigBuilder.Refinement.BW_BIN_ITP,
				search,
				XcfaConfigBuilder.PredSplit.WHOLE,
				algorithm,
				1,
				XcfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY,
				true,
				"Z3",
				"Z3"
		);

		Tuple2<Result, Optional<SafetyResult<?, ?>>> result = executeConfiguration(configuration, xcfa, (long) (30.0 / 900.0 * calculateRemainingTime()));
		if(result.get1().equals(Result.SUCCESS)) {
			checkState(result.get2().isPresent());
			logger.write(Logger.Level.MAINSTEP, "Complex portfolio successful, solver: " + configuration);
			logger.write(Logger.Level.MAINSTEP, System.lineSeparator());
		}
		return result;
	}

	////////// HELPER METHODS //////////

	private long calculateRemainingTime() {
		long remainingTime = analysisTime-(CpuTimeKeeper.getCurrentCpuTime()*1000-startCpuTime);
		if(remainingTime<=0) {
			throw new PortfolioTimeoutException("Complex portfolio timed out");
		}
		return remainingTime;
	}

}
