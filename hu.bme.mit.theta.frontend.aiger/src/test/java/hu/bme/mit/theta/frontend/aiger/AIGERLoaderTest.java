package hu.bme.mit.theta.frontend.aiger;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.frontend.aiger.impl.OptimizedAigerLoader;
import hu.bme.mit.theta.frontend.aiger.utils.AigerVisualizer;

public class AIGERLoaderTest {

	@Test
	public void testAIGERLoader() throws IOException {
		AigerLoader loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new OptimizedAigerLoader();
		final STS sts = loader.load("src/test/resources/simple3.aag");

		AigerVisualizer.visualize("src/test/resources/simple3.aag", "src/test/resources/simple3.dot");

		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
