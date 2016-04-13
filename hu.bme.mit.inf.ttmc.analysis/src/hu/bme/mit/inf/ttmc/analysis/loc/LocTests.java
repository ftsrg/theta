package hu.bme.mit.inf.ttmc.analysis.loc;

import static org.junit.Assert.assertTrue;

import java.util.Collection;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.BasicAlgorithm;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.cfa.impl.MutableCFA;

public class LocTests {

	@Test
	public void exploreLocs() {
		final CFA cfa = createSimpleCFA();
		final LocInitStates<CFALoc> initStates = new LocInitStates<>(cfa);
		final TransferRelation<LocState<CFALoc>> trel = new LocTransferRelation<>();

		//final LocState<CFALoc> initState = LocState.create(cfa.getInitLoc());
		final LocState<CFALoc> finalState = LocState.create(cfa.getFinalLoc());
		final Collection<? extends LocState<CFALoc>> reachedSet = initStates.get();
		final Algorithm<LocState<CFALoc>> algorithm = new BasicAlgorithm<>(trel);
		final Collection<LocState<CFALoc>> result = algorithm.run(reachedSet);

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
