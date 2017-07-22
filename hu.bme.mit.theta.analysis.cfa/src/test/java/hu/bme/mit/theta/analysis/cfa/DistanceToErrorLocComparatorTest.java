package hu.bme.mit.theta.analysis.cfa;

import java.util.Collections;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;

public class DistanceToErrorLocComparatorTest {

	@Test
	public void test() {
		final CFA cfa = new CFA();
		final CfaLoc loc0 = cfa.createLoc("L0");
		cfa.setInitLoc(loc0);
		final CfaLoc locErr = cfa.createLoc("LE");
		cfa.setErrorLoc(locErr);
		final CfaLoc loc1 = cfa.createLoc("L1");
		final CfaLoc loc2 = cfa.createLoc("L2");
		cfa.createEdge(loc0, loc1, Collections.emptyList());
		cfa.createEdge(loc0, loc2, Collections.emptyList());
		cfa.createEdge(loc1, loc2, Collections.emptyList());
		cfa.createEdge(loc1, locErr, Collections.emptyList());
		cfa.createEdge(loc2, locErr, Collections.emptyList());

		final Map<CfaLoc, Integer> distancesToError = DistanceToErrorLocComparator.getDistancesToError(cfa);

		Assert.assertEquals(0, (int) distancesToError.get(locErr));
		Assert.assertEquals(2, (int) distancesToError.get(loc0));
		Assert.assertEquals(1, (int) distancesToError.get(loc1));
		Assert.assertEquals(1, (int) distancesToError.get(loc2));
	}
}
