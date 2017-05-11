package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.expr.Exprs.Not;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class PonateTest {
	@Test
	public void test() {
		final RefExpr<? extends IntType> ca = Decls.Const("a", Types.Int()).getRef();
		final Expr<? extends BoolType> expr = Exprs.Eq(ca, Exprs.Int(2));

		Assert.assertEquals(expr, ExprUtils.ponate(expr));
		Assert.assertEquals(expr, ExprUtils.ponate(Not(expr)));
		Assert.assertEquals(expr, ExprUtils.ponate(Not(Not(expr))));
		Assert.assertEquals(expr, ExprUtils.ponate(Not(Not(Not(expr)))));
	}
}
