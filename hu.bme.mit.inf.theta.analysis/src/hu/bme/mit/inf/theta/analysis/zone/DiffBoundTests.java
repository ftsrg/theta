package hu.bme.mit.inf.theta.analysis.zone;

import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.add;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.asString;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.getBound;
import static hu.bme.mit.inf.theta.analysis.zone.DiffBounds.isStrict;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class DiffBoundTests {
	@Test
	public void testCompare() {
		assertTrue(Lt(0) < Inf());
		assertTrue(Lt(10) < Inf());
		assertTrue(Lt(-10) < Inf());
		assertTrue(Leq(10) < Inf());
		assertTrue(Leq(10) < Inf());
		assertTrue(Leq(-10) < Inf());

		assertTrue(Lt(0) < Lt(100));
		assertTrue(Lt(10) < Lt(100));
		assertTrue(Lt(-10) < Lt(100));
		assertTrue(Leq(0) < Lt(100));
		assertTrue(Leq(10) < Lt(100));
		assertTrue(Leq(-10) < Lt(100));

		assertTrue(Lt(0) < Leq(100));
		assertTrue(Lt(10) < Leq(100));
		assertTrue(Lt(-10) < Leq(100));
		assertTrue(Leq(0) < Leq(100));
		assertTrue(Leq(10) < Leq(100));
		assertTrue(Leq(-10) < Leq(100));

		assertTrue(Lt(-10) < Lt(10));
		assertTrue(Lt(-10) < Lt(-1));
		assertTrue(Lt(-10) < Leq(10));
		assertTrue(Lt(-10) < Leq(-1));

		assertTrue(Leq(-10) < Lt(10));
		assertTrue(Leq(-10) < Lt(-1));
		assertTrue(Leq(-10) < Leq(10));
		assertTrue(Leq(-10) < Leq(-1));

		assertTrue(Lt(0) < Leq(0));
		assertTrue(Lt(10) < Leq(10));
		assertTrue(Lt(-10) < Leq(-10));
	}

	@Test
	public void testAdd() {
		assertTrue(add(Lt(10), Lt(1)) == Lt(11));
		assertTrue(add(Leq(10), Lt(1)) == Lt(11));
		assertTrue(add(Lt(10), Leq(1)) == Lt(11));
		assertTrue(add(Leq(10), Leq(1)) == Leq(11));

		assertTrue(add(Lt(-10), Lt(-1)) == Lt(-11));
		assertTrue(add(Leq(-10), Lt(-1)) == Lt(-11));
		assertTrue(add(Lt(-10), Leq(-1)) == Lt(-11));
		assertTrue(add(Leq(-10), Leq(-1)) == Leq(-11));

		assertTrue(add(Lt(-10), Lt(1)) == Lt(-9));
		assertTrue(add(Leq(-10), Lt(1)) == Lt(-9));
		assertTrue(add(Lt(-10), Leq(1)) == Lt(-9));
		assertTrue(add(Leq(-10), Leq(1)) == Leq(-9));

		assertTrue(add(Lt(10), Lt(-1)) == Lt(9));
		assertTrue(add(Leq(10), Lt(-1)) == Lt(9));
		assertTrue(add(Lt(10), Leq(-1)) == Lt(9));
		assertTrue(add(Leq(10), Leq(-1)) == Leq(9));
	}

	@Test
	public void testIsStrict() {
		assertTrue(isStrict(Lt(0)));
		assertTrue(isStrict(Lt(10)));
		assertTrue(isStrict(Lt(-10)));
		assertFalse(isStrict(Leq(0)));
		assertFalse(isStrict(Leq(10)));
		assertFalse(isStrict(Leq(-10)));
		assertFalse(isStrict(Inf()));
	}

	@Test
	public void testGetBound() {
		assertEquals(0, getBound(Lt(0)));
		assertEquals(10, getBound(Lt(10)));
		assertEquals(-10, getBound(Lt(-10)));
		assertEquals(0, getBound(Leq(0)));
		assertEquals(10, getBound(Leq(10)));
		assertEquals(-10, getBound(Leq(-10)));
	}

	@Test
	public void testToString() {
		assertEquals("inf", asString(Inf()));
		assertEquals("(0, <)", asString(Lt(0)));
		assertEquals("(10, <)", asString(Lt(10)));
		assertEquals("(-10, <)", asString(Lt(-10)));
		assertEquals("(0, <=)", asString(Leq(0)));
		assertEquals("(10, <=)", asString(Leq(10)));
		assertEquals("(-10, <=)", asString(Leq(-10)));
	}

}
