package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.True;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class RemoveMultipleNegTests {
	@Test
	public void test() {
		Assert.assertEquals(True(), ExprUtils.removeMultipleNeg(True()));
		Assert.assertEquals(True(), ExprUtils.removeMultipleNeg(Not(Not(True()))));
		Assert.assertEquals(True(), ExprUtils.removeMultipleNeg(Not(Not(Not(Not(True()))))));
		Assert.assertEquals(Not(True()), ExprUtils.removeMultipleNeg(Not(True())));
		Assert.assertEquals(Not(True()), ExprUtils.removeMultipleNeg(Not(Not(Not(True())))));
		Assert.assertEquals(Not(True()), ExprUtils.removeMultipleNeg(Not(Not(Not(Not(Not(True())))))));
	}
}
