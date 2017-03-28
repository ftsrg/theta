package hu.bme.mit.theta.frontend.benchmark;

import java.io.FileNotFoundException;
import java.io.IOException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.frontend.aiger.impl.AigerParserSimple;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Domain;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.PredSplit;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Refinement;
import hu.bme.mit.theta.frontend.benchmark.ConfigurationBuilder.Search;
import hu.bme.mit.theta.frontend.benchmark.StsConfigurationBuilder.InitPrec;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SandBox {
	public static void main(final String[] args) throws FileNotFoundException, IOException {
		//		final StsSpec spec = StsDslManager.createStsSpec(new FileInputStream("src/test/resources/plc/REQ_3-2.system"));
		//		STS sts = spec.getAllSts().iterator().next();
		//		sts = new StsIteTransformation().transform(sts);

		System.out.println("Press a key to start");
		System.in.read();

		final STS sts = new AigerParserSimple().parse("src/test/resources/hw/nusmv.syncarb10_2.B.aag");

		System.out.println(sts);

		final Logger logger = new ConsoleLogger(2);

		final Configuration<? extends State, ? extends Action, ? extends Prec> configuration = new StsConfigurationBuilder(
				Domain.PRED, Refinement.SEQ_ITP).initPrec(InitPrec.EMPTY).search(Search.DFS)
						.predSplit(PredSplit.CONJUNCTS).logger(logger).solverFactory(Z3SolverFactory.getInstace())
						.build(sts);

		configuration.check();
	}
}
