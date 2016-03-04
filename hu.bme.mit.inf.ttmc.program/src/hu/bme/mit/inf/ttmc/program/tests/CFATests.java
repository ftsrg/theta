package hu.bme.mit.inf.ttmc.program.tests;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.impl.CFAImpl;
import hu.bme.mit.inf.ttmc.program.cfa.impl.MutableCFAImpl;
import hu.bme.mit.inf.ttmc.program.cfa.impl.MutableCFALocImpl;
import hu.bme.mit.inf.ttmc.program.utils.impl.CFAPrinter;

public class CFATests {
	
	@Test
	public void testCreation() {
		final MutableCFAImpl cfa = new MutableCFAImpl();
		final MutableCFALocImpl initLoc = cfa.getInitLoc();
		final MutableCFALocImpl finalLoc = cfa.getFinalLoc();
		final MutableCFALocImpl errorLoc = cfa.getErrorLoc();
		final MutableCFALocImpl l1 = cfa.createLoc();
		final MutableCFALocImpl l2 = cfa.createLoc();
		
		cfa.createEdge(initLoc, l1);
		cfa.createEdge(initLoc, finalLoc);
		cfa.createEdge(l1, l2);
		cfa.createEdge(l2, l1);
		cfa.createEdge(l2, l2);
		cfa.createEdge(l2, errorLoc);
		
		final CFA cfa2 = CFAImpl.copyOf(cfa);
		
		System.out.println(CFAPrinter.toGraphvizSting(cfa2));
	}
	
}
