package hu.bme.mit.inf.theta.formalism.cfa;

import org.junit.Test;

import hu.bme.mit.inf.theta.formalism.cfa.CFA;
import hu.bme.mit.inf.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.inf.theta.formalism.cfa.impl.ImmutableCfa;
import hu.bme.mit.inf.theta.formalism.cfa.impl.MutableCfa;
import hu.bme.mit.inf.theta.formalism.utils.impl.CfaPrinter;

public class CfaTests {
	
	@Test
	public void testCreation() {
		final MutableCfa cfa = new MutableCfa();
		final CfaLoc initLoc = cfa.getInitLoc();
		final CfaLoc finalLoc = cfa.getFinalLoc();
		final CfaLoc errorLoc = cfa.getErrorLoc();
		final CfaLoc l1 = cfa.createLoc();
		final CfaLoc l2 = cfa.createLoc();
		
		cfa.createEdge(initLoc, l1);
		cfa.createEdge(initLoc, finalLoc);
		cfa.createEdge(l1, l2);
		cfa.createEdge(l2, l1);
		cfa.createEdge(l2, l2);
		cfa.createEdge(l2, errorLoc);
		
		final CFA cfa2 = ImmutableCfa.copyOf(cfa);
		
		System.out.println(CfaPrinter.toGraphvizSting(cfa2));
	}
	
}
