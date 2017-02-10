package hu.bme.mit.theta.frontend.benchmark;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.common.table.impl.SimpleTableWriter;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrecision;

public class StsBenchmark {

	public static void main(final String[] args) {
		final String basePath = "/";
		final TableWriter formatter = new SimpleTableWriter(System.out, "\t");
		final int runs = 1;

		final List<StsInput> inputs = new ArrayList<>();
		inputs.add(new StsInput(basePath + "simple/boolean1.system", "safe", false));
		inputs.add(new StsInput(basePath + "simple/boolean2.system", "safe", false));
		inputs.add(new StsInput(basePath + "simple/counter.system", "safe", true));
		inputs.add(new StsInput(basePath + "simple/counter_bad.system", "safe", false));
		inputs.add(new StsInput(basePath + "simple/counter_parametric.system", "safe", true));
		inputs.add(new StsInput(basePath + "simple/loop.system", "s", true));
		inputs.add(new StsInput(basePath + "simple/loop_bad.system", "s", false));
		inputs.add(new StsInput(basePath + "simple/multipleinitial.system", "s", false));
		inputs.add(new StsInput(basePath + "simple/readerswriters.system", "s", true));
		inputs.add(new StsInput(basePath + "simple/simple1.system", "s", false));
		inputs.add(new StsInput(basePath + "simple/simple2.system", "s", true));
		inputs.add(new StsInput(basePath + "simple/simple3.system", "s", false));

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
			final int runs, final TableWriter formatter) {
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
			final TableWriter formatter) {
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
		public final String prop;
		public final boolean expected;

		public StsInput(final String path, final String prop, final boolean expected) {
			this.path = path;
			this.prop = prop;
			this.expected = expected;
		}

		public STS load() throws IOException {
			if (path.endsWith(".aag")) {
				return new AigerParserSimple().parse(path);
			} else {
				final InputStream inputStream = StsBenchmark.class.getResourceAsStream(path);
				final StsSpec spec = StsDslManager.createStsSpec(inputStream);
				final STS sts = spec.createProp(prop);
				return new StsIteTransformation().transform(sts);
			}
		}
	}
}
