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
}
