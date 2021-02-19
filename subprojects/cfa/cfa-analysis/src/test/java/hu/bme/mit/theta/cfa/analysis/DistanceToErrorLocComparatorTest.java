/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.cfa.analysis;

import java.util.Map;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Builder;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;

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
		final Loc locFinal = builder.createLoc("LF");
		builder.setFinalLoc(locFinal);
		final Stmt stmt = Stmts.Assume(BoolExprs.True());
		builder.createEdge(loc0, loc1, stmt);
		builder.createEdge(loc0, loc2, stmt);
		builder.createEdge(loc1, loc2, stmt);
		builder.createEdge(loc1, locErr, stmt);
		builder.createEdge(loc2, locErr, stmt);
		builder.createEdge(loc2, locFinal, stmt);

		final CFA cfa = builder.build();
		final Map<Loc, Integer> distancesToError = DistToErrComparator.calculateDistancesToError(cfa, cfa.getErrorLoc().get());

		Assert.assertEquals(0, (int) distancesToError.get(locErr));
		Assert.assertEquals(2, (int) distancesToError.get(loc0));
		Assert.assertEquals(1, (int) distancesToError.get(loc1));
		Assert.assertEquals(1, (int) distancesToError.get(loc2));
		Assert.assertFalse(distancesToError.containsKey(locFinal));
	}
}
