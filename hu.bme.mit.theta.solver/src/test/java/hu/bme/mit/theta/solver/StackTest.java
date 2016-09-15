package hu.bme.mit.theta.solver;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;

public class StackTest {
	@Test
	public void testPushPop() {
		final Stack<String> stack = new StackImpl<>();
		assertEquals(0, stack.toCollection().size());
		stack.push();
		assertEquals(0, stack.toCollection().size());
		stack.add("A");
		assertEquals(1, stack.toCollection().size());
		stack.add("B");
		assertEquals(2, stack.toCollection().size());
		stack.push();
		assertEquals(2, stack.toCollection().size());
		stack.add("C");
		assertEquals(3, stack.toCollection().size());
		stack.add("D");
		assertEquals(4, stack.toCollection().size());
		stack.pop();
		assertEquals(2, stack.toCollection().size());
		stack.pop();
		assertEquals(0, stack.toCollection().size());
	}

	@Test
	public void testPop2() {
		final Stack<String> stack = new StackImpl<>();
		assertEquals(0, stack.toCollection().size());
		stack.push();
		assertEquals(0, stack.toCollection().size());
		stack.add("A");
		assertEquals(1, stack.toCollection().size());
		stack.push();
		assertEquals(1, stack.toCollection().size());
		stack.add("B");
		assertEquals(2, stack.toCollection().size());
		stack.push();
		assertEquals(2, stack.toCollection().size());
		stack.add("C");
		assertEquals(3, stack.toCollection().size());
		stack.pop(2);
		assertEquals(1, stack.toCollection().size());
		stack.pop();
		assertEquals(0, stack.toCollection().size());
	}

	@Test(expected = IllegalArgumentException.class)
	public void testTooManyPop() {
		final Stack<String> stack = new StackImpl<>();

		stack.push();
		stack.push();
		stack.pop();
		stack.pop();
		stack.pop();
	}
}
