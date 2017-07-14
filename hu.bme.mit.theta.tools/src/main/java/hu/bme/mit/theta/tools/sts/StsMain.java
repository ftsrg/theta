package hu.bme.mit.theta.tools.sts;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Optional;
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
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.StsUtils;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.tools.Configuration;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.tools.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.tools.ConfigurationBuilder.Search;
import hu.bme.mit.theta.tools.sts.StsConfigurationBuilder.InitPrec;

/**
 * A command line interface for running a CEGAR configuration on an STS.
 */
public class StsMain {
	private static final String JAR_NAME = "theta-sts.jar";

	private final String[] args;
	private final TableWriter tableWriter;
	private final Options options;

	private String model;
	private String prop;
	private Domain domain;
	private Refinement refinement;
	private InitPrec initPrec;
	private Search search;
	private Optional<Boolean> expected;
	private PredSplit predSplit;
	private boolean benchmarkMode;
	private Logger logger;

	public StsMain(final String[] args) {
		this.args = args;
		tableWriter = new SimpleTableWriter(System.out, ",", "\"", "\"");
		options = new Options();
	}

	public static void main(final String[] args) {
		final StsMain mainApp = new StsMain(args);
		if (mainApp.calledWithHeaderArg()) {
			mainApp.printHeader();
			return;
		}
		try {
			mainApp.parseArgs();
		} catch (final ParseException e) {
			new HelpFormatter().printHelp(JAR_NAME, mainApp.options, true);
		}
		mainApp.runAlgorithm();
	}

	private boolean calledWithHeaderArg() {
		return args.length == 1 && "--header".equals(args[0]);
	}

	private void printHeader() {
		final String[] header = new String[] { "Result", "TimeMs", "Iterations", "ArgSize", "ArgDepth",
				"ArgMeanBranchFactor", "CexLen", "Vars", "Size" };
		for (final String str : header) {
			tableWriter.cell(str);
		}
		tableWriter.newRow();
	}

	private void parseArgs() throws ParseException {
		final Option optModel = Option.builder("m").longOpt("model").hasArg().argName("MODEL").type(String.class)
				.desc("Path of the input model").required().build();
		options.addOption(optModel);

		final Option optProp = Option.builder("p").longOpt("property").hasArg().argName("PROPERTY").type(String.class)
				.desc("Property to be verified").build();
		options.addOption(optProp);

		final Option optDomain = Option.builder("d").longOpt("domain").hasArg().argName(optionsFor(Domain.values()))
				.type(Domain.class).desc("Abstract domain").required().build();
		options.addOption(optDomain);

		final Option optRefinement = Option.builder("r").longOpt("refinement").hasArg()
				.argName(optionsFor(Refinement.values())).type(Refinement.class).desc("Refinement strategy").required()
				.build();
		options.addOption(optRefinement);

		final Option optInitPrec = Option.builder("i").longOpt("initprec").hasArg()
				.argName(optionsFor(InitPrec.values())).type(InitPrec.class).desc("Initial precision").build();
		options.addOption(optInitPrec);

		final Option optSearch = Option.builder("s").longOpt("search").hasArg().argName(optionsFor(Search.values()))
				.type(Search.class).desc("Search strategy").build();
		options.addOption(optSearch);

		final Option optPredSplit = Option.builder("ps").longOpt("predsplit").hasArg()
				.argName(optionsFor(PredSplit.values())).type(PredSplit.class).desc("Predicate splitting").build();
		options.addOption(optPredSplit);

		final Option optExpected = Option.builder("e").longOpt("expected").hasArg().argName("true|false")
				.type(Boolean.class).desc("Expected result (safe)").build();
		options.addOption(optExpected);

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
		prop = cmd.getOptionValue(optProp.getOpt(), "");
		domain = Domain.valueOf(cmd.getOptionValue(optDomain.getOpt()));
		refinement = Refinement.valueOf(cmd.getOptionValue(optRefinement.getOpt()));
		initPrec = InitPrec.valueOf(cmd.getOptionValue(optInitPrec.getOpt(), InitPrec.EMPTY.toString()));
		search = Search.valueOf(cmd.getOptionValue(optSearch.getOpt(), Search.BFS.toString()));
		expected = cmd.hasOption(optExpected.getOpt())
				? Optional.of(Boolean.parseBoolean(cmd.getOptionValue(optExpected.getOpt()))) : Optional.empty();
		predSplit = PredSplit.valueOf(cmd.getOptionValue(optPredSplit.getOpt(), PredSplit.WHOLE.toString()));
		benchmarkMode = cmd.hasOption(optBenchmark.getOpt());
		final int logLevel = Integer.parseInt(cmd.getOptionValue(optLogLevel.getOpt(), "1"));
		logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
	}

	private void runAlgorithm() {
		try {
			final STS sts = loadModel();
			final Configuration<?, ?, ?> configuration = buildConfiguration(sts);
			final SafetyResult<?, ?> status = configuration.check();
			checkResult(status);
			printResult(status, sts);
		} catch (final Throwable ex) {
			printError(ex);
		}
		if (benchmarkMode) {
			tableWriter.newRow();
		}
	}

	private STS loadModel() throws IOException {
		if (model.endsWith(".aag")) {
			return new AigerParserSimple().parse(model);
		} else if (model.endsWith(".system")) {
			final InputStream inputStream = new FileInputStream(model);
			final StsSpec spec = StsDslManager.createStsSpec(inputStream);
			return StsUtils.eliminateIte(spec.createProp(prop));
		} else {
			throw new IOException("Unknown format");
		}
	}

	private Configuration<?, ?, ?> buildConfiguration(final STS sts) {
		return new StsConfigurationBuilder(domain, refinement).initPrec(initPrec).search(search).predSplit(predSplit)
				.logger(logger).build(sts);
	}

	private void checkResult(final SafetyResult<?, ?> status) throws Exception {
		if (expected.isPresent() && !expected.get().equals(status.isSafe())) {
			throw new Exception("Expected safe = " + expected.get() + " but was " + status.isSafe());
		}
	}

	private void printResult(final SafetyResult<?, ?> status, final STS sts) {
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
			tableWriter.cell(sts.getVars().size());
			tableWriter.cell(ExprUtils.nodeCountSize(BoolExprs.And(sts.getInit(), sts.getTrans())));
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
