package hu.bme.mit.inf.theta.aiger.tests;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.theta.aiger.AIGERLoader;
import hu.bme.mit.inf.theta.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.theta.aiger.utils.AIGERVisualizer;
import hu.bme.mit.inf.theta.formalism.sts.STS;

public class AIGERLoaderTests {

	@Test
	public void testAIGERLoader() throws IOException {
		AIGERLoader loader = null;
		//loader = new AIGERLoaderSimple();
		loader = new AIGERLoaderOptimized();
		final STS sts = loader.load("instances/simple3.aag");

		AIGERVisualizer.visualize("instances/simple3.aag", "instances/simple3.dot");

		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
