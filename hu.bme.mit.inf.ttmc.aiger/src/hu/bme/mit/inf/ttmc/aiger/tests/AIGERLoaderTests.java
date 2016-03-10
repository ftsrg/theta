package hu.bme.mit.inf.ttmc.aiger.tests;

import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.aiger.AIGERLoader;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.STSFactory;
import hu.bme.mit.inf.ttmc.formalism.common.factory.impl.STSFactoryImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class AIGERLoaderTests {

	@Test
	public void testAIGERLoader() throws IOException {
		AIGERLoader loader = new AIGERLoader();
		STSFactory stsFactory = new STSFactoryImpl();
		ConstraintManager manager = new ConstraintManagerImpl();
		STS sts = loader.load("instances/flipflop.aag", stsFactory, manager);
		
		System.out.println("Vars:  " + sts.getVars());
		System.out.println("Init:  " + sts.getInit());
		System.out.println("Invar: " + sts.getInvar());
		System.out.println("Trans: " + sts.getTrans());
		System.out.println("Prop:  " + sts.getProp());
	}

}
