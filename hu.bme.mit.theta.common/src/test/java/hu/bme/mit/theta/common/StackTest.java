package hu.bme.mit.theta.common;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class StackTest {
	@Test
	public void test() {
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
}
