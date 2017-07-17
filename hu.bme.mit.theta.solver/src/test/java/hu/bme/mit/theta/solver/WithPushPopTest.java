package hu.bme.mit.theta.solver;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.solver.utils.WithPushPop;

public class WithPushPopTest {
	@Test
	public void test() {
		final SolverStub solver = new SolverStub();
		Assert.assertEquals(0, solver.nPush);
		try (WithPushPop wpp = new WithPushPop(solver)) {
			Assert.assertEquals(1, solver.nPush);
		}
		Assert.assertEquals(0, solver.nPush);
	}

	@Test
	public void testWithFunc() {
		final SolverStub solver = new SolverStub();
		Assert.assertEquals(0, solver.nPush);
		testFunc(solver);
		Assert.assertEquals(0, solver.nPush);
	}

	private void testFunc(final Solver solver) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			return;
		}
	}
}
