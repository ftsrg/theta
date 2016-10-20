package hu.bme.mit.theta.analysis.algorithm;

import static org.junit.Assert.assertEquals;

import java.util.NoSuchElementException;

import org.junit.Test;

import hu.bme.mit.theta.common.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.waitlist.LifoWaitlist;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public class WaitlistTest {

	@Test
	public void testFifo() {
		final Waitlist<String> waitlist = new FifoWaitlist<>();
		assertEquals(0, waitlist.size());

		waitlist.add("A");
		assertEquals(1, waitlist.size());

		waitlist.add("B");
		assertEquals(2, waitlist.size());

		waitlist.add("C");
		assertEquals(3, waitlist.size());

		waitlist.add("D");
		assertEquals(4, waitlist.size());

		final String item1 = waitlist.remove();
		assertEquals("A", item1);
		assertEquals(3, waitlist.size());
		assertEquals(false, waitlist.isEmpty());

		final String item2 = waitlist.remove();
		assertEquals("B", item2);
		assertEquals(2, waitlist.size());

		waitlist.add("E");
		assertEquals(3, waitlist.size());

		final String item3 = waitlist.remove();
		assertEquals("C", item3);
		assertEquals(2, waitlist.size());

		waitlist.clear();
		assertEquals(0, waitlist.size());
		assertEquals(true, waitlist.isEmpty());
	}

	@Test
	public void testLifo() {
		final Waitlist<String> waitlist = new LifoWaitlist<>();
		assertEquals(0, waitlist.size());

		waitlist.add("A");
		assertEquals(1, waitlist.size());

		waitlist.add("B");
		assertEquals(2, waitlist.size());

		waitlist.add("C");
		assertEquals(3, waitlist.size());

		waitlist.add("D");
		assertEquals(4, waitlist.size());

		final String item1 = waitlist.remove();
		assertEquals("D", item1);
		assertEquals(3, waitlist.size());
		assertEquals(false, waitlist.isEmpty());

		final String item2 = waitlist.remove();
		assertEquals("C", item2);
		assertEquals(2, waitlist.size());

		waitlist.add("E");
		assertEquals(3, waitlist.size());

		final String item3 = waitlist.remove();
		assertEquals("E", item3);
		assertEquals(2, waitlist.size());

		waitlist.clear();
		assertEquals(0, waitlist.size());
		assertEquals(true, waitlist.isEmpty());
	}

	@Test(expected = NoSuchElementException.class)
	public void testLifoException() {
		final Waitlist<String> waitlist = new LifoWaitlist<>();
		waitlist.remove();
	}

	@Test(expected = NoSuchElementException.class)
	public void testFifoException() {
		final Waitlist<String> waitlist = new FifoWaitlist<>();
		waitlist.remove();
	}
}
