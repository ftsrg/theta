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
package hu.bme.mit.theta.analysis.zone;

import static hu.bme.mit.theta.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.add;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.asString;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.getBound;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.isStrict;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.negate;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class DiffBoundTest {
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
	public void testNegate() {
		assertEquals(Lt(0), negate(Leq(0)));
		assertEquals(Leq(0), negate(Lt(0)));
		assertEquals(Lt(1), negate(Leq(-1)));
		assertEquals(Leq(1), negate(Lt(-1)));
		assertEquals(Lt(-1), negate(Leq(1)));
		assertEquals(Leq(-1), negate(Lt(1)));
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
