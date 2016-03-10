package hu.bme.mit.inf.ttmc.aiger.tests;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.aiger.AIGERLoader;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;

public class AIGERLoaderTests {

	@Test
	public void testAIGERLoader() throws IOException {
		AIGERLoader loader = new AIGERLoader();
		STSManager manager = new STSManagerImpl(new ConstraintManagerImpl());
		STS sts = loader.load("instances/flipflop.aag", manager);
		
		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
