package hu.bme.mit.theta.frontend.benchmark;

import static java.util.Collections.emptyList;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.aiger.impl.SimpleAigerLoader;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrecision;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.formatters.Formatter;
import hu.bme.mit.theta.frontend.benchmark.formatters.impl.CsvFormatter;

public class StsBenchmark {

	public static void main(final String[] args) {
		final String basePath = "src/test/resources/";
		final Formatter formatter = new CsvFormatter(new ConsoleLogger(100), "\t");
		final int runs = 1;

		final List<StsInput> inputs = new ArrayList<>();
		inputs.add(new StsInput(basePath + "simple/boolean1.system", false));
		inputs.add(new StsInput(basePath + "simple/boolean2.system", false));
		inputs.add(new StsInput(basePath + "simple/counter.system", true));
		inputs.add(new StsInput(basePath + "simple/counter_bad.system", false));
		inputs.add(new StsInput(basePath + "simple/counter_parametric.system", true));
		inputs.add(new StsInput(basePath + "simple/loop.system", true));
		inputs.add(new StsInput(basePath + "simple/loop_bad.system", false));
		inputs.add(new StsInput(basePath + "simple/multipleinitial.system", false));
		inputs.add(new StsInput(basePath + "simple/readerswriters.system", true));
		inputs.add(new StsInput(basePath + "simple/simple1.system", false));
		inputs.add(new StsInput(basePath + "simple/simple2.system", true));
		inputs.add(new StsInput(basePath + "simple/simple3.system", false));

		final List<StsConfigurationBuilder> builders = new ArrayList<>();
		//@formatter:off
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.CRAIG_ITP).initPrecision(InitPrecision.EMPTY).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.CRAIG_ITP).initPrecision(InitPrecision.EMPTY).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.CRAIG_ITP).initPrecision(InitPrecision.PROP).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.CRAIG_ITP).initPrecision(InitPrecision.PROP).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.SEQ_ITP).initPrecision(InitPrecision.EMPTY).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.SEQ_ITP).initPrecision(InitPrecision.EMPTY).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.SEQ_ITP).initPrecision(InitPrecision.PROP).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.PRED, Refinement.SEQ_ITP).initPrecision(InitPrecision.PROP).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.CRAIG_ITP).initPrecision(InitPrecision.EMPTY).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.CRAIG_ITP).initPrecision(InitPrecision.EMPTY).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.CRAIG_ITP).initPrecision(InitPrecision.PROP).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.CRAIG_ITP).initPrecision(InitPrecision.PROP).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.SEQ_ITP).initPrecision(InitPrecision.EMPTY).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.SEQ_ITP).initPrecision(InitPrecision.EMPTY).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.SEQ_ITP).initPrecision(InitPrecision.PROP).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.SEQ_ITP).initPrecision(InitPrecision.PROP).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.UNSAT_CORE).initPrecision(InitPrecision.EMPTY).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.UNSAT_CORE).initPrecision(InitPrecision.EMPTY).search(Search.DFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.UNSAT_CORE).initPrecision(InitPrecision.PROP).search(Search.BFS));
		builders.add(new StsConfigurationBuilder(Domain.EXPL, Refinement.UNSAT_CORE).initPrecision(InitPrecision.PROP).search(Search.DFS));
		//@formatter:on

		run(inputs, builders, runs, formatter);
	}

	private static void run(final Collection<StsInput> inputs, final Collection<StsConfigurationBuilder> builders,
			final int runs, final Formatter formatter) {
		System.out.println(String.format("Running %d configurations on %d inputs with %d repetitions.", builders.size(),
				inputs.size(), runs));

		formatter.cell("Model").cell("IsSafe").cell("Domain").cell("Refinement").cell("Initital precision")
				.cell("Search strategy").cell("Time (ms)").cell("Iterations").cell("ARG size").cell("ARG depth")
				.cell("Cex length").newRow();

		for (final StsInput input : inputs) {
			for (final StsConfigurationBuilder builder : builders) {
				for (int i = 0; i < runs; ++i) {
					run(input, builder, formatter);
				}
			}
		}
		System.out.println("DONE");
	}

	private static void run(final StsInput input, final StsConfigurationBuilder configBuilder,
			final Formatter formatter) {
		formatter.cell(input.path);
		formatter.cell(input.expected + "");
		formatter.cell(configBuilder.getDomain() + "");
		formatter.cell(configBuilder.getRefinement() + "");
		formatter.cell(configBuilder.getInitPrecision() + "");
		formatter.cell(configBuilder.getSearch() + "");
		try {
			final STS sts = input.load();
			final Configuration<?, ?, ?> configuration = configBuilder.build(sts);
			final SafetyStatus<?, ?> status = configuration.check();

			if (status.isSafe() != input.expected) {
				formatter.cell("FALSE", 5);
			} else {
				final Statistics stats = status.getStats().get();
				final ARG<?, ?> arg = status.getArg();

				formatter.cell(stats.getElapsedMillis() + "");
				formatter.cell(stats.getIterations() + "");
				formatter.cell(arg.size() + "");
				formatter.cell(arg.getDepth() + "");
				if (status.isUnsafe()) {
					formatter.cell(status.asUnsafe().getTrace().length() + "");
				} else {
					formatter.cell("");
				}
			}

		} catch (final IOException e) {
			formatter.cell("IO EXCEPTION", 5);
		} catch (final Exception e) {
			formatter.cell("EXCEPTION", 5);
		}
		formatter.newRow();

	}

	public static class StsInput {
		public final String path;
		public final boolean expected;

		public StsInput(final String path, final boolean expected) {
			this.path = path;
			this.expected = expected;
		}

		public STS load() throws IOException {
			if (path.endsWith(".aag")) {
				return new SimpleAigerLoader().load(path);
			} else {
				final StsSpec spec = StsDslManager.parse(path, emptyList());
				if (spec.getAllSts().size() != 1) {
					throw new IOException("File must contain exactly one STS.");
				}
				return new StsIteTransformation().transform(spec.getAllSts().iterator().next());
			}
		}
	}
}
