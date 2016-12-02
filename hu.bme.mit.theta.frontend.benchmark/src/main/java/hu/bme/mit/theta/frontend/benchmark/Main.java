package hu.bme.mit.theta.frontend.benchmark;

import static java.util.Collections.emptyList;

import java.io.IOException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.aiger.impl.SimpleAigerLoader;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrecision;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Search;

public class Main {

	public static void main(final String[] args) {
		final Options options = new Options();

		final Option optModel = new Option("m", "model", true, "Path of the input model");
		optModel.setRequired(true);
		optModel.setArgName("MODEL");
		options.addOption(optModel);

		final Option optDomain = new Option("d", "domain", true, "Abstract domain");
		optDomain.setRequired(true);
		optDomain.setArgName("DOMAIN");
		options.addOption(optDomain);

		final Option optRefinement = new Option("r", "refinement", true, "Refinement strategy");
		optRefinement.setRequired(true);
		optRefinement.setArgName("REFINEMENT");
		options.addOption(optRefinement);

		final Option optInitPrecision = new Option("i", "initprec", true, "Initial precision");
		optInitPrecision.setArgName("INITPRECISION");
		options.addOption(optInitPrecision);

		final Option optSearch = new Option("s", "search", true, "Search strategy");
		optSearch.setArgName("SEARCH");
		options.addOption(optSearch);

		final CommandLineParser parser = new DefaultParser();
		final HelpFormatter helpFormatter = new HelpFormatter();
		final CommandLine cmd;

		try {
			cmd = parser.parse(options, args);
		} catch (final ParseException e) {
			helpFormatter.printHelp("theta.jar", options, true);
			return;
		}

		final String model = cmd.getOptionValue(optModel.getOpt());
		final Domain domain = Domain.valueOf(cmd.getOptionValue(optDomain.getOpt()));
		final Refinement refinement = Refinement.valueOf(cmd.getOptionValue(optRefinement.getOpt()));

		final InitPrecision initPrecision = InitPrecision
				.valueOf(cmd.getOptionValue(optInitPrecision.getOpt(), InitPrecision.EMPTY.toString()));
		final Search search = Search.valueOf(cmd.getOptionValue(optSearch.getOpt(), Search.BFS.toString()));

		final TableWriter formatter = new SimpleTableWriter(System.out, ";");

		try {

			formatter.cell(model).cell(domain.toString()).cell(refinement.toString()).cell(initPrecision.toString())
					.cell(search.toString());

			STS sts = null;

			if (model.endsWith(".aag")) {
				sts = new SimpleAigerLoader().load(model);
			} else {
				final StsSpec spec = StsDslManager.parse(model, emptyList());
				if (spec.getAllSts().size() != 1) {
					throw new IOException("File must contain exactly one STS.");
				}
				sts = new StsIteTransformation().transform(spec.getAllSts().iterator().next());
			}

			final Configuration<?, ?, ?> configuration = new StsConfigurationBuilder(domain, refinement)
					.initPrecision(initPrecision).search(search).build(sts);
			final SafetyStatus<?, ?> status = configuration.check();
			final Statistics stats = status.getStats().get();

			formatter.cell(status.isSafe() + "").cell(stats.getElapsedMillis() + "").cell(stats.getIterations() + "")
					.cell(status.getArg().size() + "").cell(status.getArg().getDepth() + "");

			if (status.isUnsafe()) {
				formatter.cell(status.asUnsafe().getTrace().length() + "");
			}
			System.out.println();

		} catch (final Exception ex) {
			formatter.cell("EX: " + ex.getClass().getSimpleName());
		}

		formatter.newRow();
	}

}
