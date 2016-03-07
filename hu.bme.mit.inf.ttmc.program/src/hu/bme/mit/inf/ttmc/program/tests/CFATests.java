package hu.bme.mit.inf.ttmc.program.tests;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.impl.ImmutableCFA;
import hu.bme.mit.inf.ttmc.program.cfa.impl.MutableCFA;
import hu.bme.mit.inf.ttmc.program.cfa.impl.MutableCFALoc;
import hu.bme.mit.inf.ttmc.program.utils.impl.CFAPrinter;

public class CFATests {
	
	@Test
	public void testCreation() {
		final MutableCFA cfa = new MutableCFA();
		final MutableCFALoc initLoc = cfa.getInitLoc();
		final MutableCFALoc finalLoc = cfa.getFinalLoc();
		final MutableCFALoc errorLoc = cfa.getErrorLoc();
		final MutableCFALoc l1 = cfa.createLoc();
		final MutableCFALoc l2 = cfa.createLoc();
		
		cfa.createEdge(initLoc, l1);
		cfa.createEdge(initLoc, finalLoc);
		cfa.createEdge(l1, l2);
		cfa.createEdge(l2, l1);
		cfa.createEdge(l2, l2);
		cfa.createEdge(l2, errorLoc);
		
		final CFA cfa2 = ImmutableCFA.copyOf(cfa);
		
		System.out.println(CFAPrinter.toGraphvizSting(cfa2));
	}
	
}
