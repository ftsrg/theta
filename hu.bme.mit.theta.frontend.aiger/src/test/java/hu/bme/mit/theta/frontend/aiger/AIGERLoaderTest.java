package hu.bme.mit.theta.frontend.aiger;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.frontend.aiger.AIGERLoader;
import hu.bme.mit.theta.frontend.aiger.impl.AIGERLoaderOptimized;
import hu.bme.mit.theta.frontend.aiger.utils.AIGERVisualizer;

public class AIGERLoaderTest {

	@Test
	public void testAIGERLoader() throws IOException {
		AIGERLoader loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new AIGERLoaderOptimized();
		final STS sts = loader.load("src/test/resources/simple3.aag");

		AIGERVisualizer.visualize("src/test/resources/simple3.aag", "src/test/resources/simple3.dot");

		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
