package hu.bme.mit.inf.ttmc.program.tests;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.program.tcfa.impl.MutableTCFAImpl;
import hu.bme.mit.inf.ttmc.program.tcfa.impl.MutableTCFALocImpl;
import hu.bme.mit.inf.ttmc.program.utils.impl.TCFAPrinter;

public class MutableTCFAImplTests {
	
	@Test
	public void testCreation() {
		final ConstraintManager manager = new ConstraintManagerImpl();
		final MutableTCFAImpl tcfa = new MutableTCFAImpl(manager);
		final MutableTCFALocImpl initLoc = tcfa.getInitLoc();
		final MutableTCFALocImpl finalLoc = tcfa.getFinalLoc();
		final MutableTCFALocImpl errorLoc = tcfa.getErrorLoc();
		final MutableTCFALocImpl l1 = tcfa.createLoc();
		final MutableTCFALocImpl l2 = tcfa.createLoc();
		
		tcfa.createEdge(initLoc, l1);
		tcfa.createEdge(initLoc, finalLoc);
		tcfa.createEdge(l1, l2);
		tcfa.createEdge(l2, l1);
		tcfa.createEdge(l2, l2);
		tcfa.createEdge(l2, errorLoc);
		
		System.out.println(TCFAPrinter.toGraphvizSting(tcfa));
	}
	
}
