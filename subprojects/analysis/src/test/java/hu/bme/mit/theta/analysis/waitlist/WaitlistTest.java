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
package hu.bme.mit.theta.analysis.waitlist;

import static org.junit.Assert.assertEquals;

import java.util.NoSuchElementException;

import org.junit.Assert;
import org.junit.Test;

public class WaitlistTest {

	@Test
	public void testFifo() {
		final Waitlist<String> waitlist = FifoWaitlist.create();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());

		waitlist.add("A");
		assertEquals(1, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("B");
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("C");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("D");
		assertEquals(4, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item1 = waitlist.remove();
		assertEquals("A", item1);
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item2 = waitlist.remove();
		assertEquals("B", item2);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("E");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item3 = waitlist.remove();
		assertEquals("C", item3);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.clear();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());
	}

	@Test
	public void testLifo() {
		final Waitlist<String> waitlist = LifoWaitlist.create();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());

		waitlist.add("A");
		assertEquals(1, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("B");
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("C");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("D");
		assertEquals(4, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item1 = waitlist.remove();
		assertEquals("D", item1);
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item2 = waitlist.remove();
		assertEquals("C", item2);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("E");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item3 = waitlist.remove();
		assertEquals("E", item3);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.clear();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());
	}

	@Test
	public void testPriority() {
		final Waitlist<String> waitlist = PriorityWaitlist.create();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());

		waitlist.add("C");
		assertEquals(1, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("A");
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("D");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("B");
		assertEquals(4, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item1 = waitlist.remove();
		assertEquals("A", item1);
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item2 = waitlist.remove();
		assertEquals("B", item2);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.add("E");
		assertEquals(3, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		final String item3 = waitlist.remove();
		assertEquals("C", item3);
		assertEquals(2, waitlist.size());
		Assert.assertFalse(waitlist.isEmpty());

		waitlist.clear();
		assertEquals(0, waitlist.size());
		Assert.assertTrue(waitlist.isEmpty());
	}

	@Test(expected = NoSuchElementException.class)
	public void testLifoException() {
		final Waitlist<String> waitlist = LifoWaitlist.create();
		waitlist.remove();
	}

	@Test(expected = NoSuchElementException.class)
	public void testFifoException() {
		final Waitlist<String> waitlist = FifoWaitlist.create();
		waitlist.remove();
	}

	@Test(expected = NoSuchElementException.class)
	public void testPriorityException() {
		final Waitlist<String> waitlist = PriorityWaitlist.create();
		waitlist.remove();
	}

	@Test
	public void testRandomSeed() {
		final long seed = 1234;
		final Waitlist<String> wl1 = RandomWaitlist.create(seed);
		final Waitlist<String> wl2 = RandomWaitlist.create(seed);

		for (int i = 1; i <= 10; ++i) {
			final String item = "item" + i;
			wl1.add(item);
			wl2.add(item);
		}

		while (!wl1.isEmpty() && !wl2.isEmpty()) {
			Assert.assertEquals(wl1.remove(), wl2.remove());
		}

		Assert.assertTrue(wl1.isEmpty());
		Assert.assertTrue(wl2.isEmpty());
	}
}
