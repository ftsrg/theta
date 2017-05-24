package hu.bme.mit.theta.frontend.benchmark.sts;

import java.io.FileInputStream;
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
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.utils.impl.ExprMetrics;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.frontend.benchmark.Configuration;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.sts.StsConfigurationBuilder.InitPrec;

/**
 * A command line interface for running a CEGAR configuration on an STS. The
 * output is a single row containing parameters of the configuration and the
 * model, and output metrics.
 */
public class StsMain {

	public static void main(final String[] args) {
		final TableWriter tableWriter = new SimpleTableWriter(System.out, ",", "\"", "\"");

		// If only called with a single --header argument, print header and exit
		if (args.length == 1 && "--header".equals(args[0])) {
			tableWriter.cell("Safe");
			tableWriter.cell("TimeMs");
			tableWriter.cell("Iterations");
			tableWriter.cell("ArgSize");
			tableWriter.cell("ArgDepth");
			tableWriter.cell("ArgMeanBranchFactor");
			tableWriter.cell("CexLen");
			tableWriter.cell("Vars");
			tableWriter.cell("Size");
			tableWriter.newRow();
			return;
		}

		// Setting up argument parser
		final Options options = new Options();

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
		final HelpFormatter helpFormatter = new HelpFormatter();
		final CommandLine cmd;

		// Parse arguments
		try {
			cmd = parser.parse(options, args);
		} catch (final ParseException e) {
			helpFormatter.printHelp("theta.jar", options, true);
			return;
		}

		// Convert string arguments to the proper values
		final String model = cmd.getOptionValue(optModel.getOpt());
		final Domain domain = Domain.valueOf(cmd.getOptionValue(optDomain.getOpt()));
		final Refinement refinement = Refinement.valueOf(cmd.getOptionValue(optRefinement.getOpt()));
		final InitPrec initPrec = InitPrec.valueOf(cmd.getOptionValue(optInitPrec.getOpt(), InitPrec.EMPTY.toString()));
		final Search search = Search.valueOf(cmd.getOptionValue(optSearch.getOpt(), Search.BFS.toString()));
		final Optional<Boolean> expected = cmd.hasOption(optExpected.getOpt())
				? Optional.of(Boolean.parseBoolean(cmd.getOptionValue(optExpected.getOpt()))) : Optional.empty();
		final PredSplit predSplit = PredSplit
				.valueOf(cmd.getOptionValue(optPredSplit.getOpt(), PredSplit.WHOLE.toString()));
		final boolean benchmarkMode = cmd.hasOption(optBenchmark.getOpt());

		final int logLevel = Integer.parseInt(cmd.getOptionValue(optLogLevel.getOpt(), "1"));
		final Logger logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);

		// Run the algorithm
		try {
			// Read input model
			STS sts = null;
			if (model.endsWith(".aag")) {
				sts = new AigerParserSimple().parse(model);
			} else {
				final String prop = cmd.getOptionValue(optProp.getOpt());
				final InputStream inputStream = new FileInputStream(model);
				final StsSpec spec = StsDslManager.createStsSpec(inputStream);
				sts = new StsIteTransformation().transform(spec.createProp(prop));
			}

			// Build configuration
			final Configuration<?, ?, ?> configuration = new StsConfigurationBuilder(domain, refinement)
					.initPrec(initPrec).search(search).predSplit(predSplit).logger(logger).build(sts);
			// Run algorithm
			final SafetyResult<?, ?> status = configuration.check();
			final CegarStatistics stats = (CegarStatistics) status.getStats().get();

			// Check result
			if (expected.isPresent() && !expected.get().equals(status.isSafe())) {
				throw new Exception("Expected safe = " + expected.get() + " but was " + status.isSafe());
			}

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
				tableWriter.cell(ExprUtils.size(Exprs.And(sts.getInit(), sts.getTrans()), ExprMetrics.absoluteSize()));
			}

		} catch (final Throwable ex) {
			final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
			if (benchmarkMode) {
				tableWriter.cell("[EX] " + ex.getClass().getSimpleName() + message);
			} else {
				logger.writeln("Exception occured: " + ex.getClass().getSimpleName(), 0);
				logger.writeln("Message: " + ex.getMessage(), 0, 1);
			}

		}
		if (benchmarkMode) {
			tableWriter.newRow();
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
