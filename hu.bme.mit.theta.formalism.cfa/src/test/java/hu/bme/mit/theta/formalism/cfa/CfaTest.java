package hu.bme.mit.theta.formalism.cfa;

import org.junit.Test;

import hu.bme.mit.theta.common.visualization.GraphVizWriter;
import hu.bme.mit.theta.formalism.cfa.impl.ImmutableCfa;
import hu.bme.mit.theta.formalism.cfa.impl.MutableCfa;
import hu.bme.mit.theta.formalism.cfa.utils.CfaVisualizer;

public class CfaTest {

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

		System.out.println(new GraphVizWriter().writeString(CfaVisualizer.visualize(cfa2)));
	}

}
