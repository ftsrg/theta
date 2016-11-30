package hu.bme.mit.theta.frontend.benchmark;

import static java.util.Collections.emptyList;

import java.io.FileNotFoundException;
import java.io.IOException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Search;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SandBox {
	public static void main(final String[] args) throws FileNotFoundException, IOException {
		final StsSpec spec = StsDslManager.parse("src/test/resources/simple/simple3.system", emptyList());
		STS sts = spec.getAllSts().iterator().next();
		sts = new StsIteTransformation().transform(sts);

		final Logger logger = new ConsoleLogger(100);

		final Configuration<? extends State, ? extends Action, ? extends Precision> configuration = new StsConfigurationBuilder(
				Domain.EXPL, Refinement.CRAIGITP).logger(logger).search(Search.BFS)
						.solverFactory(Z3SolverFactory.getInstace()).build(sts);

		final SafetyStatus<? extends State, ? extends Action> status = configuration.check();
		System.out.println(status);
	}
}
