package hu.bme.mit.theta.formalism.cfa.analysis;

import java.util.Collections;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Builder;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public class DistanceToErrorLocComparatorTest {

	@Test
	public void test() {
		final Builder builder = CFA.builder();
		final Loc loc0 = builder.createLoc("L0");
		builder.setInitLoc(loc0);
		final Loc locErr = builder.createLoc("LE");
		builder.setErrorLoc(locErr);
		final Loc loc1 = builder.createLoc("L1");
		final Loc loc2 = builder.createLoc("L2");
		builder.setFinalLoc(loc2);
		builder.createEdge(loc0, loc1, Collections.emptyList());
		builder.createEdge(loc0, loc2, Collections.emptyList());
		builder.createEdge(loc1, loc2, Collections.emptyList());
		builder.createEdge(loc1, locErr, Collections.emptyList());
		builder.createEdge(loc2, locErr, Collections.emptyList());

		final CFA cfa = builder.build();
		final Map<Loc, Integer> distancesToError = DistToErrComparator.getDistancesToError(cfa);

		Assert.assertEquals(0, (int) distancesToError.get(locErr));
		Assert.assertEquals(2, (int) distancesToError.get(loc0));
		Assert.assertEquals(1, (int) distancesToError.get(loc1));
		Assert.assertEquals(1, (int) distancesToError.get(loc2));
	}
}
