package hu.bme.mit.theta.frontend.benchmark;

import java.io.FileNotFoundException;
import java.io.IOException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.frontend.aiger.impl.SimpleAigerLoader;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrecision;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.Search;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SandBox {
	public static void main(final String[] args) throws FileNotFoundException, IOException {
		// final StsSpec spec =
		// StsDslManager.parse("src/test/resources/simple/multipleinitial.system",
		// Collections.emptyList());
		// STS sts = spec.getAllSts().iterator().next();
		// sts = new StsIteTransformation().transform(sts);

		final STS sts = new SimpleAigerLoader().load("src/test/resources/hw/srg5ptimonegnv.aag");

		System.out.println(sts);

		final Logger logger = new ConsoleLogger(2);

		final Configuration<? extends State, ? extends Action, ? extends Precision> configuration = new StsConfigurationBuilder(
				Domain.EXPL, Refinement.SEQ_ITP).initPrecision(InitPrecision.PROP).logger(logger).search(Search.BFS)
						.solverFactory(Z3SolverFactory.getInstace()).build(sts);

		final SafetyStatus<? extends State, ? extends Action> status = configuration.check();
		System.out.println(status);
		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(status.getArg())));
		System.out.println(status.getArg().size());
	}
}
