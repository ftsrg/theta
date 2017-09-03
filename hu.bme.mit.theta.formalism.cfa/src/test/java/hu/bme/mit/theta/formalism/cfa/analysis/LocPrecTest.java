package hu.bme.mit.theta.formalism.cfa.analysis;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.Builder;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.ConstCfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.GenericCfaPrec;

public class LocPrecTest {

	public static class PrecStub implements Prec {

	}

	private final PrecStub p0 = new PrecStub();
	private final PrecStub p1 = new PrecStub();
	private final PrecStub p2 = new PrecStub();

	@Test
	public void testConstLocPrec() {
		final ConstCfaPrec<PrecStub> cp = ConstCfaPrec.create(p1);
		final ConstCfaPrec<PrecStub> r1 = cp.refine(p1);
		final ConstCfaPrec<PrecStub> r2 = cp.refine(p2);
		final ConstCfaPrec<PrecStub> r3 = r2.refine(p2);

		Assert.assertTrue(cp == r1);
		Assert.assertTrue(r1 != r2);
		Assert.assertTrue(r2 == r3);
	}

	@Test
	public void testConstLocPrecEquals() {
		final ConstCfaPrec<PrecStub> cp1 = ConstCfaPrec.create(p1);
		final ConstCfaPrec<PrecStub> cp2 = ConstCfaPrec.create(p1);
		final ConstCfaPrec<PrecStub> cp3 = ConstCfaPrec.create(p2);

		Assert.assertEquals(cp1, cp2);
		Assert.assertNotEquals(cp1, cp3);
		Assert.assertNotEquals(cp2, cp3);
	}

	@Test
	public void testGenericLocPrec() {
		final GenericCfaPrec<PrecStub> gp = GenericCfaPrec.create(p0);
		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");
		final Loc l2 = builder.createLoc("L2");

		Assert.assertEquals(p0, gp.getPrec(l1));
		Assert.assertEquals(p0, gp.getPrec(l2));

		final GenericCfaPrec<PrecStub> r1 = gp.refine(l1, p1);

		Assert.assertEquals(p1, r1.getPrec(l1));
		Assert.assertEquals(p0, r1.getPrec(l2));

		final GenericCfaPrec<PrecStub> r2 = r1.refine(l2, p2);

		Assert.assertEquals(p1, r2.getPrec(l1));
		Assert.assertEquals(p2, r2.getPrec(l2));
	}

	@Test
	public void testGenericLocPrecEquals() {
		final GenericCfaPrec<PrecStub> gp0 = GenericCfaPrec.create(p0);
		final GenericCfaPrec<PrecStub> gp1 = GenericCfaPrec.create(p0);
		final GenericCfaPrec<PrecStub> gp2 = GenericCfaPrec.create(p1);

		Assert.assertEquals(gp0, gp1);
		Assert.assertNotEquals(gp0, gp2);
		Assert.assertNotEquals(gp1, gp2);

		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");
		final Loc l2 = builder.createLoc("L2");

		final GenericCfaPrec<PrecStub> gp0r0 = gp0.refine(l1, p1);
		final GenericCfaPrec<PrecStub> gp1r0 = gp1.refine(l1, p1);

		Assert.assertEquals(gp0r0, gp1r0);

		final GenericCfaPrec<PrecStub> gp0r1 = gp0r0.refine(l2, p1);
		final GenericCfaPrec<PrecStub> gp1r1 = gp1r0.refine(l2, p2);

		Assert.assertNotEquals(gp0r1, gp1r1);
	}

	@Test
	public void testGenericLocPrecEquals2() {
		final Builder builder = CFA.builder();
		final Loc l1 = builder.createLoc("L1");

		final GenericCfaPrec<PrecStub> original = GenericCfaPrec.create(p0);
		final GenericCfaPrec<PrecStub> refined = original.refine(l1, p1);
		final GenericCfaPrec<PrecStub> refinedBack = refined.refine(l1, p0);

		Assert.assertEquals(original, refinedBack);

	}
}
