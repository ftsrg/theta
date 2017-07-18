package hu.bme.mit.theta.tools.cfa;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.beust.jcommander.ParametersDelegate;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarStatistics;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.tools.CegarParams;
import hu.bme.mit.theta.tools.Configuration;
import hu.bme.mit.theta.tools.cfa.CfaConfigurationBuilder.PrecGranularity;

/**
 * A command line interface for running a CEGAR configuration on a CFA.
 */
public class CfaMain {
	private static final String JAR_NAME = "theta-cfa.jar";
	private final String[] args;
	private final TableWriter writer;

	@ParametersDelegate
	CegarParams cegarParams = new CegarParams();

	@Parameter(names = { "-m", "--model" }, description = "Path of the input model", required = true)
	String model;

	@Parameter(names = { "-g", "--precision-granularity" }, description = "Precision granularity")
	PrecGranularity precGranularity = PrecGranularity.CONST;

	@Parameter(names = { "-ll", "--loglevel" }, description = "Detailedness of logging")
	Integer logLevel = 1;

	@Parameter(names = { "-bm", "--benchmark" }, description = "Benchmark mode (only print metrics)")
	Boolean benchmarkMode = false;

	@Parameter(names = { "--header" }, description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;

	private Logger logger;

	public CfaMain(final String[] args) {
		this.args = args;
		writer = new SimpleTableWriter(System.out, ",", "\"", "\"");
	}

	public static void main(final String[] args) {
		final CfaMain mainApp = new CfaMain(args);
		mainApp.run();
	}

	private void run() {
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
			logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
		} catch (final ParameterException ex) {
			System.out.println(ex.getMessage());
			ex.usage();
			return;
		}

		if (headerOnly) {
			printHeader();
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
			writer.newRow();
		}
	}

	private void printHeader() {
		final String[] header = new String[] { "Result", "TimeMs", "Iterations", "ArgSize", "ArgDepth",
				"ArgMeanBranchFactor", "CexLen", "Vars", "Locs", "Edges" };
		for (final String str : header) {
			writer.cell(str);
		}
		writer.newRow();
	}

	private CFA loadModel() throws IOException {
		final InputStream inputStream = new FileInputStream(model);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		return cfa;
	}

	private Configuration<?, ?, ?> buildConfiguration(final CFA cfa) {
		return new CfaConfigurationBuilder(cegarParams.getDomain(), cegarParams.getRefinement())
				.precGranularity(precGranularity).search(cegarParams.getSearch()).predSplit(cegarParams.getPredSplit())
				.logger(logger).build(cfa);
	}

	private void printResult(final SafetyResult<?, ?> status, final CFA cfa) {
		final CegarStatistics stats = (CegarStatistics) status.getStats().get();
		if (benchmarkMode) {
			writer.cell(status.isSafe());
			writer.cell(stats.getElapsedMillis());
			writer.cell(stats.getIterations());
			writer.cell(status.getArg().size());
			writer.cell(status.getArg().getDepth());
			writer.cell(status.getArg().getMeanBranchingFactor());
			if (status.isUnsafe()) {
				writer.cell(status.asUnsafe().getTrace().length() + "");
			} else {
				writer.cell("");
			}
			writer.cell(cfa.getVars().size());
			writer.cell(cfa.getLocs().size());
			writer.cell(cfa.getEdges().size());
		}
	}

	private void printError(final Throwable ex) {
		final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
		if (benchmarkMode) {
			writer.cell("[EX] " + ex.getClass().getSimpleName() + message);
		} else {
			logger.writeln("Exception occured: " + ex.getClass().getSimpleName(), 0);
			logger.writeln("Message: " + ex.getMessage(), 0, 1);
		}
	}
}
