package hu.bme.mit.theta.formalism.sts.aiger;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;

public class AIGERLoaderTest {

	@Test
	public void testAIGERLoader() throws IOException {
		AigerParser loader = null;
		// loader = new AIGERLoaderSimple();
		loader = new CompactingAigerParser();
		final STS sts = loader.parse("src/test/resources/simple3.aag");
		System.out.println(sts);
	}

}
