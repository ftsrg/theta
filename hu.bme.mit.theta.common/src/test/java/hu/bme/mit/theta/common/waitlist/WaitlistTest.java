package hu.bme.mit.theta.common.waitlist;

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
}
