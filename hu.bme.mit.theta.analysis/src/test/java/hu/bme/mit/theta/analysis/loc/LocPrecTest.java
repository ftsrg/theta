package hu.bme.mit.theta.analysis.loc;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.stubs.EdgeStub;
import hu.bme.mit.theta.analysis.stubs.LocStub;
import hu.bme.mit.theta.analysis.stubs.PrecStub;

public class LocPrecTest {
	private final PrecStub p0 = new PrecStub();
	private final PrecStub p1 = new PrecStub();
	private final PrecStub p2 = new PrecStub();

	@Test
	public void testConstLocPrec() {
		final ConstLocPrec<PrecStub, ?, ?> cp = ConstLocPrec.create(p1);
		final ConstLocPrec<PrecStub, ?, ?> r1 = cp.refine(p1);
		final ConstLocPrec<PrecStub, ?, ?> r2 = cp.refine(p2);
		final ConstLocPrec<PrecStub, ?, ?> r3 = r2.refine(p2);

		Assert.assertTrue(cp == r1);
		Assert.assertTrue(r1 != r2);
		Assert.assertTrue(r2 == r3);
	}

	@Test
	public void testConstLocPrecEquals() {
		final ConstLocPrec<PrecStub, ?, ?> cp1 = ConstLocPrec.create(p1);
		final ConstLocPrec<PrecStub, ?, ?> cp2 = ConstLocPrec.create(p1);
		final ConstLocPrec<PrecStub, ?, ?> cp3 = ConstLocPrec.create(p2);

		Assert.assertEquals(cp1, cp2);
		Assert.assertNotEquals(cp1, cp3);
		Assert.assertNotEquals(cp2, cp3);
	}

	@Test
	public void testGenericLocPrec() {
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp = GenericLocPrec.create(p0);
		final LocStub l1 = new LocStub();
		final LocStub l2 = new LocStub();

		Assert.assertEquals(p0, gp.getPrec(l1));
		Assert.assertEquals(p0, gp.getPrec(l2));

		final GenericLocPrec<PrecStub, LocStub, EdgeStub> r1 = gp.refine(l1, p1);

		Assert.assertEquals(p1, r1.getPrec(l1));
		Assert.assertEquals(p0, r1.getPrec(l2));

		final GenericLocPrec<PrecStub, LocStub, EdgeStub> r2 = r1.refine(l2, p2);

		Assert.assertEquals(p1, r2.getPrec(l1));
		Assert.assertEquals(p2, r2.getPrec(l2));
	}

	@Test
	public void testGenericLocPrecEquals() {
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp0 = GenericLocPrec.create(p0);
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp1 = GenericLocPrec.create(p0);
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp2 = GenericLocPrec.create(p1);

		Assert.assertEquals(gp0, gp1);
		Assert.assertNotEquals(gp0, gp2);
		Assert.assertNotEquals(gp1, gp2);

		final LocStub l1 = new LocStub();
		final LocStub l2 = new LocStub();

		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp0r0 = gp0.refine(l1, p1);
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp1r0 = gp1.refine(l1, p1);

		Assert.assertEquals(gp0r0, gp1r0);

		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp0r1 = gp0r0.refine(l2, p1);
		final GenericLocPrec<PrecStub, LocStub, EdgeStub> gp1r1 = gp1r0.refine(l2, p2);

		Assert.assertNotEquals(gp0r1, gp1r1);

	}
}
