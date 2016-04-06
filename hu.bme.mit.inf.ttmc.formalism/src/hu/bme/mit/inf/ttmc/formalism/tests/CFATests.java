package hu.bme.mit.inf.ttmc.formalism.tests;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.ImmutableCFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.MutableCFA;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CFAPrinter;

public class CFATests {
	
	@Test
	public void testCreation() {
		final MutableCFA cfa = new MutableCFA();
		final CFALoc initLoc = cfa.getInitLoc();
		final CFALoc finalLoc = cfa.getFinalLoc();
		final CFALoc errorLoc = cfa.getErrorLoc();
		final CFALoc l1 = cfa.createLoc();
		final CFALoc l2 = cfa.createLoc();
		
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
