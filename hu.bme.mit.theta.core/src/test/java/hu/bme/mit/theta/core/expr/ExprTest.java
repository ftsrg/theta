package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import org.junit.Assert;
import org.junit.Test;

public class ExprTest {

	@Test
	public void testPrime() {
		Assert.assertEquals(Prime(Int(1)), Prime(Int(1), 1));
		Assert.assertEquals(Prime(Prime(Int(1))), Prime(Int(1), 2));
		Assert.assertEquals(Prime(Prime(Prime(Int(1)))), Prime(Int(1), 3));
	}

}
