package hu.bme.mit.theta.core.expr;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.expr.impl.Exprs;

public class ExprTest {

	@Test
	public void testPrime() {
		Assert.assertEquals(Exprs.Prime(Exprs.Int(1)), Exprs.Prime(Exprs.Int(1), 1));
		Assert.assertEquals(Exprs.Prime(Exprs.Prime(Exprs.Int(1))), Exprs.Prime(Exprs.Int(1), 2));
		Assert.assertEquals(Exprs.Prime(Exprs.Prime(Exprs.Prime(Exprs.Int(1)))), Exprs.Prime(Exprs.Int(1), 3));
	}

}
