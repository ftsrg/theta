package hu.bme.mit.theta.xcfa.algorithmselection;

import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.NotSolvableException;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfig;
import hu.bme.mit.theta.cfa.analysis.config.CfaConfigBuilder;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class PortfolioHandler {
	public static final PortfolioHandler instance = new PortfolioHandler();
	private static final List<Configuration> configurationList = new ArrayList<>();
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
			ArgCexCheckHandler.instance.setArgCexCheck(true);
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

	private static class Configuration {
		public final CfaConfigBuilder.Domain domain;
		public final CfaConfigBuilder.Refinement refinement;
		public final CfaConfigBuilder.PrecGranularity precGranularity;
		public final CfaConfigBuilder.Search search;
		public final CfaConfigBuilder.PredSplit predSplit;
		public final int maxEnum;
		public final CfaConfigBuilder.InitPrec initPrec;
		public final PruneStrategy pruneStrategy;

		Configuration(CfaConfigBuilder.Domain domain,
					  CfaConfigBuilder.Refinement refinement,
					  CfaConfigBuilder.PrecGranularity precGranularity,
					  CfaConfigBuilder.Search search,
					  CfaConfigBuilder.PredSplit predSplit,
					  int maxEnum,
					  CfaConfigBuilder.InitPrec initPrec,
					  PruneStrategy pruneStrategy) {
			this.domain = domain;
			this.refinement = refinement;
			this.precGranularity = precGranularity;
			this.search = search;
			this.predSplit = predSplit;
			this.maxEnum = maxEnum;
			this.initPrec = initPrec;
			this.pruneStrategy = pruneStrategy;
		}

		public CfaConfig<?, ?, ?> buildConfiguration(CFA cfa, CFA.Loc errLoc, Logger.Level logLevel) throws Exception {
			try {
				return new CfaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance())
						.precGranularity(precGranularity).search(search)
						.predSplit(predSplit).encoding(CfaConfigBuilder.Encoding.LBE).maxEnum(maxEnum).initPrec(initPrec)
						.pruneStrategy(pruneStrategy).logger(new ConsoleLogger(logLevel)).build(cfa, errLoc);

			} catch (final Exception ex) {
				throw new Exception("Could not create configuration: " + ex.getMessage(), ex);
			}

			// if(ArchitectureConfig.arithmetic == ArchitectureConfig.ArithmeticType.bitvector) {}
			// return buildIntegerConfiguration(cfa, loc);
		}

		@Override
		public String toString() {
			return "Configuration{" +
					"domain=" + domain +
					", refinement=" + refinement +
					", precGranularity=" + precGranularity +
					", search=" + search +
					", predSplit=" + predSplit +
					", maxEnum=" + maxEnum +
					", initPrec=" + initPrec +
					", pruneStrategy=" + pruneStrategy +
					'}';
		}
	}
}
