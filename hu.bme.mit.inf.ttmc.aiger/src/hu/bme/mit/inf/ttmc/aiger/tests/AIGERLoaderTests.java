package hu.bme.mit.inf.ttmc.aiger.tests;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.aiger.AIGERLoader;
import hu.bme.mit.inf.ttmc.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.inf.ttmc.aiger.utils.AIGERVisualizer;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;

public class AIGERLoaderTests {

	@Test
	public void testAIGERLoader() throws IOException {
		AIGERLoader loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new AIGERLoaderOptimized();
		final STSManager manager = new STSManagerImpl();
		final STS sts = loader.load("instances/simple3.aag", manager);

		AIGERVisualizer.visualize("instances/simple3.aag", "instances/simple3.dot");

		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
