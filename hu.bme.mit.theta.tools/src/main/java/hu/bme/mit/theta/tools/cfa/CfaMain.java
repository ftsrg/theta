package hu.bme.mit.theta.tools.cfa;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.tools.Configuration;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.tools.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Search;
import hu.bme.mit.theta.tools.cfa.CfaConfigurationBuilder.PrecGranularity;

/**
 * A command line interface for running a CEGAR configuration on a CFA.
 */
public class CfaMain {
	private static final String JAR_NAME = "theta-cfa.jar";
	private final String[] args;
	private final TableWriter tableWriter;

	@Parameter(names = { "-m", "--model" }, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = { "-d", "--domain" }, description = "Abstract domain", required = true)
	Domain domain;

	@Parameter(names = { "-r", "--refinement" }, description = "Refinement strategy", required = true)
	Refinement refinement;

	@Parameter(names = { "-g", "--precision-granularity" }, description = "Precision granularity")
	PrecGranularity precGranularity = PrecGranularity.CONST;

	@Parameter(names = { "-s", "--search" }, description = "Search strategy")
	Search search = Search.BFS;

	@Parameter(names = { "-ps", "--predsplit" }, description = "Predicate splitting")
	PredSplit predSplit = PredSplit.WHOLE;

	@Parameter(names = { "-ll", "--loglevel" }, description = "Detailedness of logging")
	Integer logLevel = 1;

	@Parameter(names = { "-bm", "--benchmark" }, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	private Logger logger;

	public CfaMain(final String[] args) {
		this.args = args;
		tableWriter = new SimpleTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final CfaMain mainApp = new CfaMain(args);
		mainApp.run();
	}

	private void run() {
		if (calledWithHeaderArg()) {
			printHeader();
			return;
		}
		try {
			final JCommander cmd = JCommander.newBuilder().addObject(this).build();
			cmd.setProgramName(JAR_NAME);
			cmd.parse(args);
			logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
		} catch (final ParameterException ex) {
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}
		try {
			final CFA cfa = loadModel();
			final Configuration<?, ?, ?> configuration = buildConfiguration(cfa);
			final SafetyResult<?, ?> status = configuration.check();
			printResult(status, cfa);
		} catch (final Throwable ex) {
			printError(ex);
		}
		if (benchmarkMode) {
			tableWriter.newRow();
		}
	}

	private boolean calledWithHeaderArg() {
		return args.length == 1 && "--header".equals(args[0]);
	}

	private void printHeader() {
		final String[] header = new String[] { "Result", "TimeMs", "Iterations", "ArgSize", "ArgDepth",
				"ArgMeanBranchFactor", "CexLen", "Vars", "Locs", "Edges" };
		for (final String str : header) {
			tableWriter.cell(str);
		}
		tableWriter.newRow();
	}

	private CFA loadModel() throws IOException {
		final InputStream inputStream = new FileInputStream(model);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		return cfa;
	}

	private Configuration<?, ?, ?> buildConfiguration(final CFA cfa) {
		return new CfaConfigurationBuilder(domain, refinement).precGranularity(precGranularity).search(search)
				.predSplit(predSplit).logger(logger).build(cfa);
	}

	private void printResult(final SafetyResult<?, ?> status, final CFA cfa) {
		final CegarStatistics stats = (CegarStatistics) status.getStats().get();
		if (benchmarkMode) {
			tableWriter.cell(status.isSafe());
			tableWriter.cell(stats.getElapsedMillis());
			tableWriter.cell(stats.getIterations());
			tableWriter.cell(status.getArg().size());
			tableWriter.cell(status.getArg().getDepth());
			tableWriter.cell(status.getArg().getMeanBranchingFactor());
			if (status.isUnsafe()) {
				tableWriter.cell(status.asUnsafe().getTrace().length() + "");
			} else {
				tableWriter.cell("");
			}
			tableWriter.cell(cfa.getVars().size());
			tableWriter.cell(cfa.getLocs().size());
			tableWriter.cell(cfa.getEdges().size());
		}
	}

	private void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		if (benchmarkMode) {
			tableWriter.cell("[EX] " + ex.getClass().getSimpleName() + message);
		} else {
			logger.writeln("Exception occured: " + ex.getClass().getSimpleName(), 0);
			logger.writeln("Message: " + ex.getMessage(), 0, 1);
		}
	}
}
