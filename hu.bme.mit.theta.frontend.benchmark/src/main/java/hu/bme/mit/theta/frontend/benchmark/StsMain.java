package hu.bme.mit.theta.frontend.benchmark;

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
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.utils.impl.ExprMetrics;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrec;

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

		final Option optModel = new Option("m", "model", true, "Path of the input model");
		optModel.setRequired(true);
		optModel.setArgName("MODEL");
		options.addOption(optModel);

		final Option optProp = new Option("p", "property", true, "Property to be verified");
		optProp.setArgName("PROPERTY");
		options.addOption(optProp);

		final Option optDomain = new Option("d", "domain", true, "Abstract domain");
		optDomain.setRequired(true);
		optDomain.setArgName(options(Domain.values()));
		options.addOption(optDomain);

		final Option optRefinement = new Option("r", "refinement", true, "Refinement strategy");
		optRefinement.setRequired(true);
		optRefinement.setArgName(options(Refinement.values()));
		options.addOption(optRefinement);

		final Option optInitPrec = new Option("i", "initprec", true, "Initial precision");
		optInitPrec.setArgName(options(InitPrec.values()));
		options.addOption(optInitPrec);

		final Option optSearch = new Option("s", "search", true, "Search strategy");
		optSearch.setArgName(options(Search.values()));
		options.addOption(optSearch);

		final Option optPredSplit = new Option("ps", "predsplit", true, "Predicate split");
		optPredSplit.setArgName(options(PredSplit.values()));
		options.addOption(optPredSplit);

		final Option optExpected = new Option("e", "expected", true, "Expected result (safe)");
		optExpected.setArgName("true|false");
		options.addOption(optExpected);

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
					.initPrec(initPrec).search(search).predSplit(predSplit).build(sts);
			// Run algorithm
			final SafetyResult<?, ?> status = configuration.check();
			final Statistics stats = status.getStats().get();

			// Check result
			if (expected.isPresent() && !expected.get().equals(status.isSafe())) {
				throw new Exception("Expected safe = " + expected.get() + " but was " + status.isSafe());
			}

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
			tableWriter.cell(ExprUtils.size(Exprs.And(Exprs.And(sts.getInit()), Exprs.And(sts.getTrans())),
					ExprMetrics.absoluteSize()));

		} catch (final Exception ex) {
			final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
			tableWriter.cell("[EX] " + ex.getClass().getSimpleName() + message);
		}

		tableWriter.newRow();
	}

	private static String options(final Object[] objs) {
		final StringJoiner sj = new StringJoiner("|");
		for (final Object o : objs) {
			sj.add(o.toString());
		}
		return sj.toString();
	}
}
