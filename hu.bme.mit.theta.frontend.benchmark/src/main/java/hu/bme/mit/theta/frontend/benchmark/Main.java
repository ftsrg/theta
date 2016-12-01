package hu.bme.mit.theta.frontend.benchmark;

import static java.util.Collections.emptyList;

import java.io.IOException;

import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
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
		String model = null;
		StsConfigurationBuilder.Domain domain = null;
		StsConfigurationBuilder.Refinement refinement = null;
		StsConfigurationBuilder.InitPrecision initPrecision = InitPrecision.EMPTY;
		StsConfigurationBuilder.Search search = Search.BFS;

		try {
			for (int i = 0; i < args.length; i += 2) {
				if (args[i].equals("-m")) {
					model = args[i + 1];
				} else if (args[i].equals("-d")) {
					domain = Domain.valueOf(args[i + 1]);
				} else if (args[i].equals("-r")) {
					refinement = Refinement.valueOf(args[i + 1]);
				} else if (args[i].equals("-i")) {
					initPrecision = InitPrecision.valueOf(args[i + 1]);
				} else if (args[i].equals("-s")) {
					search = Search.valueOf(args[i + 1]);
				}
			}

			System.out.print(String.format("%s,%s,%s,%s,%s", model, domain, refinement, initPrecision, search));

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
			System.out.print(String.format(",%s,%d,%d,%d,%d", status.isSafe() + "", stats.getElapsedMillis(),
					stats.getIterations(), status.getArg().size(), status.getArg().getDepth()));
			if (status.isUnsafe()) {
				System.out.print("," + status.asUnsafe().getTrace().length());
			}
			System.out.println();

		} catch (final Exception ex) {
			System.out.println(",EX: " + ex.getClass().getSimpleName());
			ex.printStackTrace();
		}
	}

}
