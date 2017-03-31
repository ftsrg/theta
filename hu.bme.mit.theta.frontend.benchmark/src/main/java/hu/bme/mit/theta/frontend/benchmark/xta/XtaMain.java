package hu.bme.mit.theta.frontend.benchmark.xta;

import java.io.FileInputStream;
import java.io.InputStream;
import java.util.StringJoiner;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpStatistics;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.dsl.XtaDslManager;
import hu.bme.mit.theta.frontend.benchmark.xta.XtaConfiguration.Algorithm;

public final class XtaMain {

	private static final Option ALGORITHM = Option.builder("a").longOpt("algorithm").numberOfArgs(1)
			.argName(optionsFor(Algorithm.values())).type(Algorithm.class).desc("Algorithm").required().build();

	private static final Option MODEL = Option.builder("m").longOpt("model").numberOfArgs(1).argName("MODEL")
			.type(String.class).desc("Path of the input model").required().build();

	private static final Option STRATEGY = Option.builder("s").longOpt("strategy").numberOfArgs(1)
			.argName(optionsFor(SearchStrategy.values())).type(SearchStrategy.class).desc("Search strategy").required()
			.build();

	public static void main(final String[] args) {
		final TableWriter writer = new SimpleTableWriter(System.out, ",", "\"", "\"");

		// Setting up argument parser
		final Options options = new Options();

		options.addOption(MODEL);
		options.addOption(ALGORITHM);
		options.addOption(STRATEGY);

		final CommandLineParser parser = new DefaultParser();
		final HelpFormatter helpFormatter = new HelpFormatter();
		final CommandLine cmd;

		// Parse arguments
		try {
			cmd = parser.parse(options, args);
		} catch (final ParseException e) {
			// If called with a single --header argument, print header and exit
			if (args.length == 1 && "--header".equals(args[0])) {
				writer.cell("AlgorithmTimeInMs");
				writer.cell("RefinementTimeInMs");
				writer.cell("InterpolationTimeInMs");
				writer.cell("RefinementSteps");
				writer.cell("ArgDepth");
				writer.cell("ArgNodes");
				writer.cell("ArgNodesExpanded");
				writer.newRow();
				return;
			} else {
				helpFormatter.printHelp("theta-xta.jar", options, true);
				return;
			}
		}

		final String modelOption = cmd.getOptionValue(MODEL.getOpt());
		final XtaSystem system;
		try {
			final InputStream inputStream = new FileInputStream(modelOption);
			system = XtaDslManager.createSystem(inputStream);
		} catch (final Exception e) {
			System.out.println("Path \"" + modelOption + "\" is invalid");
			return;
		}

		final String algorithmOption = cmd.getOptionValue(ALGORITHM.getOpt());
		final Algorithm algorithm;
		try {
			algorithm = Enum.valueOf(Algorithm.class, algorithmOption);
		} catch (final Exception e) {
			System.out.println("\"" + algorithmOption + "\" is not a valid value for --algorithm");
			return;
		}

		final String strategyOption = cmd.getOptionValue(STRATEGY.getOpt());
		final SearchStrategy strategy;
		try {
			strategy = Enum.valueOf(SearchStrategy.class, strategyOption);
		} catch (final Exception e) {
			System.out.println("\"" + strategyOption + "\" is not a valid value for --strategy");
			return;
		}

		try {
			final XtaConfiguration configuration = XtaConfiguration.create(system, l -> false, algorithm, strategy);

			final SafetyChecker<?, ?, UnitPrec> checker = configuration.getChecker();
			final SafetyResult<?, ?> result = checker.check(UnitPrec.getInstance());
			final ARG<?, ?> arg = result.getArg();
			final XtaItpStatistics stats = (XtaItpStatistics) result.getStats().get();

			writer.cell(stats.getAlgorithmTimeInMs());
			writer.cell(stats.getRefinementTimeInMs());
			writer.cell(stats.getInterpolationTimeInMs());
			writer.cell(stats.getRefinementSteps());
			writer.cell(arg.getDepth());
			writer.cell(arg.getNodes().count());
			writer.cell(arg.getNodes().filter(ArgNode::isExpanded).count());

		} catch (final Exception e) {
			final String message = e.getMessage() == null ? "" : ": " + e.getMessage();
			writer.cell("[EX] " + e.getClass().getSimpleName() + message);
		}

		writer.newRow();
	}

	private static String optionsFor(final Object[] objs) {
		final StringJoiner sj = new StringJoiner("|");
		for (final Object o : objs) {
			sj.add(o.toString());
		}
		return sj.toString();
	}

}
