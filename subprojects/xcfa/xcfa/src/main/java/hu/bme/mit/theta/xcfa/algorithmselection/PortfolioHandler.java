package hu.bme.mit.theta.xcfa.algorithmselection;

import com.google.common.util.concurrent.SimpleTimeLimiter;
import com.google.common.util.concurrent.TimeLimiter;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class PortfolioHandler {
/*
	public static final PortfolioHandler instance = new PortfolioHandler();
	private static final List<CegarConfiguration> configurationList = new ArrayList<>();
	private File statisticsfile;

	static {
		configurationList.add(new Configuration(CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY));
		configurationList.add(new Configuration(CfaConfigBuilder.Domain.EXPL,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.ALLVARS,
				PruneStrategy.LAZY));
		configurationList.add(new Configuration(CfaConfigBuilder.Domain.PRED_CART,
				CfaConfigBuilder.Refinement.BW_BIN_ITP,
				CfaConfigBuilder.PrecGranularity.GLOBAL,
				CfaConfigBuilder.Search.ERR,
				CfaConfigBuilder.PredSplit.WHOLE,
				1,
				CfaConfigBuilder.InitPrec.EMPTY,
				PruneStrategy.LAZY));
	}

	public hu.bme.mit.theta.analysis.algorithm.SafetyResult<?,?> executeAnalysis(CFA cfa, Logger.Level logLevel, String statistics) {
		if(statistics==null) statisticsfile = null;
		else statisticsfile = new File(statistics);
		writeCfaStatistics(cfa);

		for (Configuration configuration : configurationList) {
			if(configuration.refinement.equals(CfaConfigBuilder.Refinement.MULTI_SEQ)) {
				ArgCexCheckHandler.instance.setArgCexCheck(true, true);
			} else {
				ArgCexCheckHandler.instance.setArgCexCheck(true, false);
			}
			try {
				System.out.println(configuration);
				statisticsPrint(configuration.toString());
				return configuration.buildConfiguration(cfa, cfa.getErrorLoc().get(), logLevel).check();
			} catch (final NotSolvableException exception) {
				System.err.println(exception.getMessage());
				statisticsPrint(exception.getMessage());
				System.err.println("Configuration failed, starting next one");
				statisticsPrint("Configuration failed, starting next one");
			} catch (final Exception ex) {
				String message = ex.getMessage() == null ? "(no message)" : ex.getMessage();
				System.err.println("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message);
				statisticsPrint("Error while running algorithm: " + ex.getClass().getSimpleName() + " " + message);
				System.err.println("Configuration failed, starting next one");
				statisticsPrint("Configuration failed, starting next one");
			}
		}

		System.err.println("All configurations failed, task not solvable by portfolio");
		statisticsPrint("All configurations failed");
		// throw new RuntimeException("All configurations failed");
		System.exit(-42); // TODO here for benchexec reasons; tool info should be changed instead
		throw new RuntimeException("All configurations failed");
	}

	private void statisticsPrint(String string) {
		if(statisticsfile!=null) {
			BufferedWriter bw = null;
			try {
				bw = new BufferedWriter(new FileWriter(statisticsfile));
				bw.write(string);
				bw.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	};

	private void writeCfaStatistics(CFA cfa) {
		if(statisticsfile!=null) {
			BufferedWriter bw = null;
			try {
				bw = new BufferedWriter(new FileWriter(statisticsfile));

				bw.write("CFA-data varCount " + cfa.getVars().size() + System.lineSeparator());
				bw.write("CFA-data locCount " + cfa.getLocs().size() + System.lineSeparator());
				bw.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	private enum Result { UNKNOWN, TIMEOUT, STUCK, SUCCESS }

	private Tuple2<Result, SafetyResult<?,?>> executeConfiguration(CegarConfiguration configuration, Logger.Level logLevel, CFA cfa, long timeout) {
		try {
			TimeLimiter limiter = new SimpleTimeLimiter();
			SafetyResult<?, ?> safetyResult = configuration.buildConfiguration(cfa, cfa.getErrorLoc().get(), logLevel).check();

			if(safetyResult.isSafe() || safetyResult.isUnsafe()) {
				return Tuple2.of(Result.SUCCESS, safetyResult);
			}
		} catch (final NotSolvableException exception) {
			return Tuple2.of(Result.STUCK, null);
		} catch (final Exception ex) {
			return Tuple2.of(Result.UNKNOWN, null);
		}
	}
*/
}
