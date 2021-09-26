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

import hu.bme.mit.theta.core.decl.VarDecl;
import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.CFA.Builder;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.cfa.analysis.prec.LocalCfaPrec;

import java.util.Collection;
import java.util.Set;

public class LocPrecTest {
	private final PrecStub p0 = new PrecStub();
	private final PrecStub p1 = new PrecStub();
	private final PrecStub p2 = new PrecStub();

	public static class PrecStub implements Prec {
		@Override
		public Collection<VarDecl<?>> getUsedVars() {
			return Set.of();
		}
	}

	@Test
	public void testConstLocPrec() {
		final GlobalCfaPrec<PrecStub> cp = GlobalCfaPrec.create(p1);
		final GlobalCfaPrec<PrecStub> r1 = cp.refine(p1);
		final GlobalCfaPrec<PrecStub> r2 = cp.refine(p2);
		final GlobalCfaPrec<PrecStub> r3 = r2.refine(p2);

		Assert.assertSame(cp, r1);
		Assert.assertNotSame(r1, r2);
		Assert.assertSame(r2, r3);
	}

	@Test
	public void testConstLocPrecEquals() {
		final GlobalCfaPrec<PrecStub> cp1 = GlobalCfaPrec.create(p1);
		final GlobalCfaPrec<PrecStub> cp2 = GlobalCfaPrec.create(p1);
		final GlobalCfaPrec<PrecStub> cp3 = GlobalCfaPrec.create(p2);

		Assert.assertEquals(cp1, cp2);
		Assert.assertNotEquals(cp1, cp3);
		Assert.assertNotEquals(cp2, cp3);
	}

	@Test
	public void testGenericLocPrec() {
		final LocalCfaPrec<PrecStub> gp = LocalCfaPrec.create(p0);
		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");
		final Loc l2 = builder.createLoc("L2");

		Assert.assertEquals(p0, gp.getPrec(l1));
		Assert.assertEquals(p0, gp.getPrec(l2));

		final LocalCfaPrec<PrecStub> r1 = gp.refine(l1, p1);

		Assert.assertEquals(p1, r1.getPrec(l1));
		Assert.assertEquals(p0, r1.getPrec(l2));

		final LocalCfaPrec<PrecStub> r2 = r1.refine(l2, p2);

		Assert.assertEquals(p1, r2.getPrec(l1));
		Assert.assertEquals(p2, r2.getPrec(l2));
	}

	@Test
	public void testGenericLocPrecEquals() {
		final LocalCfaPrec<PrecStub> gp0 = LocalCfaPrec.create(p0);
		final LocalCfaPrec<PrecStub> gp1 = LocalCfaPrec.create(p0);
		final LocalCfaPrec<PrecStub> gp2 = LocalCfaPrec.create(p1);

		Assert.assertEquals(gp0, gp1);
		Assert.assertNotEquals(gp0, gp2);
		Assert.assertNotEquals(gp1, gp2);

		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");
		final Loc l2 = builder.createLoc("L2");

		final LocalCfaPrec<PrecStub> gp0r0 = gp0.refine(l1, p1);
		final LocalCfaPrec<PrecStub> gp1r0 = gp1.refine(l1, p1);

		Assert.assertEquals(gp0r0, gp1r0);

		final LocalCfaPrec<PrecStub> gp0r1 = gp0r0.refine(l2, p1);
		final LocalCfaPrec<PrecStub> gp1r1 = gp1r0.refine(l2, p2);

		Assert.assertNotEquals(gp0r1, gp1r1);
	}

	@Test
	public void testGenericLocPrecEquals2() {
		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");

		final LocalCfaPrec<PrecStub> original = LocalCfaPrec.create(p0);
		final LocalCfaPrec<PrecStub> refined = original.refine(l1, p1);
		final LocalCfaPrec<PrecStub> refinedBack = refined.refine(l1, p0);

		Assert.assertEquals(original, refinedBack);

	}
}
