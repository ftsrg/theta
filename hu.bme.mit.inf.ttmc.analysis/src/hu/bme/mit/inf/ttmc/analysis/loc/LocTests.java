package hu.bme.mit.inf.ttmc.analysis.loc;

import static org.junit.Assert.assertTrue;

import java.util.Collection;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.BasicAlgorithm;
import hu.bme.mit.inf.ttmc.analysis.impl.NullPrecision;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFAEdge;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.MutableCFA;

public class LocTests {

	@Test
	public void exploreLocs() {
		final CFA cfa = createSimpleCFA();

		final LocAbstraction<CFALoc, CFAEdge> locAbstraction = CFALocAbstraction.create(cfa);

		final LocState<CFALoc> finalState = LocState.create(cfa.getFinalLoc());
		final Algorithm<LocState<CFALoc>, NullPrecision> algorithm = new BasicAlgorithm<>(LocDomain.create(), locAbstraction);
		final Collection<LocState<CFALoc>> result = algorithm.run(NullPrecision.get());

		assertTrue(result.contains(finalState));
	}

	private static CFA createSimpleCFA() {
		final MutableCFA cfa = new MutableCFA();
		final CFALoc begin = cfa.getInitLoc();
		final CFALoc end = cfa.getFinalLoc();
		final CFALoc l1 = cfa.createLoc();
		final CFALoc l2 = cfa.createLoc();
		cfa.createEdge(begin, l1);
		cfa.createEdge(l1, begin);
		cfa.createEdge(l1, l2);
		cfa.createEdge(l2, end);
		return cfa;
	}

}
