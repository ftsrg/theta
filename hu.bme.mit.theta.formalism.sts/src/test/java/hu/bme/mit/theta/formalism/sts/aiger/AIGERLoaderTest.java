package hu.bme.mit.theta.formalism.sts.aiger;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.aiger.AigerParser;
import hu.bme.mit.theta.formalism.sts.aiger.AigerParserOptimized;
import hu.bme.mit.theta.formalism.sts.aiger.AigerVisualizer;

public class AIGERLoaderTest {

	@Test
	public void testAIGERLoader() throws IOException {
		AigerParser loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new AigerParserOptimized();
		final STS sts = loader.parse("src/test/resources/simple3.aag");

		AigerVisualizer.visualize("src/test/resources/simple3.aag", "src/test/resources/simple3.dot");

		System.out.println(sts);
	}

}
