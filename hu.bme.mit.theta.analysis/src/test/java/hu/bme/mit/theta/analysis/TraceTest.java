package hu.bme.mit.theta.analysis;

import static com.google.common.collect.ImmutableList.of;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;

public class TraceTest {
	State s0 = new StateStub("S0");
	State s1 = new StateStub("S1");
	State s2 = new StateStub("S2");
	Action a0 = new ActionStub("A0");
	Action a1 = new ActionStub("A1");

	@Test
	public void testSizes() {
		final Trace<?, ?> trace = Trace.of(of(s0, s1, s2), of(a0, a1));
		Assert.assertEquals(trace.length(), trace.getActions().size());
		Assert.assertEquals(trace.length() + 1, trace.getStates().size());
	}

	@Test
	public void testReverse() {
		final Trace<?, ?> trace = Trace.of(of(s0, s1, s2), of(a0, a1));
		final Trace<?, ?> reverse = trace.reverse();

		Assert.assertEquals(trace.length(), reverse.length());
		Assert.assertEquals(trace.getStates().size(), reverse.getStates().size());
		Assert.assertEquals(trace.getActions().size(), reverse.getActions().size());

		Assert.assertEquals(s2, reverse.getState(0));
		Assert.assertEquals(s1, reverse.getState(1));
		Assert.assertEquals(s0, reverse.getState(2));
		Assert.assertEquals(a1, reverse.getAction(0));
		Assert.assertEquals(a0, reverse.getAction(1));

		Assert.assertEquals(trace, trace.reverse().reverse());
		Assert.assertNotEquals(trace, trace.reverse());
	}

	@Test
	public void testEquals() {
		final Trace<?, ?> trace1 = Trace.of(of(s0, s1, s2), of(a0, a1));
		final Trace<?, ?> trace2 = Trace.of(of(s0, s1, s2), of(a0, a1));
		final Trace<?, ?> trace3 = Trace.of(of(s0, s2, s1), of(a0, a1));
		final Trace<?, ?> trace4 = Trace.of(of(s0, s1, s2), of(a1, a0));

		Assert.assertTrue(trace1.equals(trace2));
		Assert.assertFalse(trace1.equals(trace3));
		Assert.assertFalse(trace1.equals(trace4));
	}
}
