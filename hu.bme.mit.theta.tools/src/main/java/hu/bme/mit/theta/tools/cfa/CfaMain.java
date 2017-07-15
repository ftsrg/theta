package hu.bme.mit.theta.tools.cfa;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.StringJoiner;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

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
	private final Options options;

	private String model;
	private Domain domain;
	private Refinement refinement;
	private PrecGranularity precGranularity;
	private Search search;
	private PredSplit predSplit;
	private boolean benchmarkMode;
	private Logger logger;

	public CfaMain(final String[] args) {
		this.args = args;
		tableWriter = new SimpleTableWriter(System.out, ",", "\"", "\"");
		options = new Options();
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
			parseArgs();
		} catch (final ParseException e) {
			new HelpFormatter().printHelp(JAR_NAME, options, true);
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

	private void parseArgs() throws ParseException {
		final Option optModel = Option.builder("m").longOpt("model").hasArg().argName("MODEL").type(String.class)
				.desc("Path of the input model").required().build();
		options.addOption(optModel);

		final Option optDomain = Option.builder("d").longOpt("domain").hasArg().argName(optionsFor(Domain.values()))
				.type(Domain.class).desc("Abstract domain").required().build();
		options.addOption(optDomain);

		final Option optRefinement = Option.builder("r").longOpt("refinement").hasArg()
				.argName(optionsFor(Refinement.values())).type(Refinement.class).desc("Refinement strategy").required()
				.build();
		options.addOption(optRefinement);

		final Option optPrecGran = Option.builder("g").longOpt("precision-granularity").hasArg()
				.argName(optionsFor(PrecGranularity.values())).type(PrecGranularity.class).desc("Precision granularity")
				.build();
		options.addOption(optPrecGran);

		final Option optSearch = Option.builder("s").longOpt("search").hasArg().argName(optionsFor(Search.values()))
				.type(Search.class).desc("Search strategy").build();
		options.addOption(optSearch);

		final Option optPredSplit = Option.builder("ps").longOpt("predsplit").hasArg()
				.argName(optionsFor(PredSplit.values())).type(PredSplit.class).desc("Predicate splitting").build();
		options.addOption(optPredSplit);

		final Option optLogLevel = Option.builder("ll").longOpt("loglevel").hasArg().argName("INT").type(Integer.class)
				.desc("Level of logging (detailedness)").build();
		options.addOption(optLogLevel);

		final Option optBenchmark = Option.builder("bm").longOpt("benchmark")
				.desc("Benchmark mode (only print output values)").build();
		options.addOption(optBenchmark);

		final CommandLineParser parser = new DefaultParser();
		final CommandLine cmd = parser.parse(options, args);

		// Convert string arguments to the proper values
		model = cmd.getOptionValue(optModel.getOpt());
		domain = Domain.valueOf(cmd.getOptionValue(optDomain.getOpt()));
		refinement = Refinement.valueOf(cmd.getOptionValue(optRefinement.getOpt()));
		precGranularity = PrecGranularity
				.valueOf(cmd.getOptionValue(optPrecGran.getOpt(), PrecGranularity.CONST.toString()));
		search = Search.valueOf(cmd.getOptionValue(optSearch.getOpt(), Search.BFS.toString()));
		predSplit = PredSplit.valueOf(cmd.getOptionValue(optPredSplit.getOpt(), PredSplit.WHOLE.toString()));
		benchmarkMode = cmd.hasOption(optBenchmark.getOpt());
		final int logLevel = Integer.parseInt(cmd.getOptionValue(optLogLevel.getOpt(), "1"));
		logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
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

	private static String optionsFor(final Object[] objs) {
		final StringJoiner sj = new StringJoiner("|");
		for (final Object o : objs) {
			sj.add(o.toString());
		}
		return sj.toString();
	}
}
