package hu.bme.mit.theta.frontend.benchmark;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.StsSpec;
import hu.bme.mit.theta.formalism.sts.utils.impl.StsIteTransformation;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.sts.StsConfigurationBuilder;
import hu.bme.mit.theta.frontend.benchmark.sts.StsConfigurationBuilder.InitPrec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SandBox {
	public static void main(final String[] args) throws FileNotFoundException, IOException {
		final StsSpec spec = StsDslManager
				.createStsSpec(new FileInputStream("src/test/resources/simple/simple2.system"));
		STS sts = spec.getAllSts().iterator().next();
		sts = new StsIteTransformation().transform(sts);

		System.out.println("Press a key to start");
		System.in.read();

		//		final STS sts = new AigerParserSimple().parse("src/test/resources/hw/srg5ptimo.aag");

		System.out.println(sts);

		final Logger logger = new ConsoleLogger(100);

		final Configuration<? extends State, ? extends Action, ? extends Prec> configuration = new StsConfigurationBuilder(
				Domain.PRED, Refinement.BW_BIN_ITP).initPrec(InitPrec.EMPTY).search(Search.BFS)
						.predSplit(PredSplit.WHOLE).logger(logger).solverFactory(Z3SolverFactory.getInstace())
						.build(sts);

		configuration.check();
	}
}
