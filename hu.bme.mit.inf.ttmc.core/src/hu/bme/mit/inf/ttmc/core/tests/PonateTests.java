package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.True;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class PonateTests {
	@Test
	public void test() {
		Assert.assertEquals(True(), ExprUtils.ponate(True()));
		Assert.assertEquals(True(), ExprUtils.ponate(Not(True())));
		Assert.assertEquals(True(), ExprUtils.ponate(Not(Not(True()))));
		Assert.assertEquals(True(), ExprUtils.ponate(Not(Not(Not(True())))));
	}
}
