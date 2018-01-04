package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class ExplSplittersTest {
	private final Expr<BoolType> x = Decls.Var("x", Bool()).getRef();
	private final Expr<BoolType> y = Decls.Var("y", Bool()).getRef();
	private final Expr<BoolType> z = Decls.Var("z", Bool()).getRef();
	private final Expr<BoolType> expr = And(Not(x), Or(Not(y), z));

	@Test
	public void testWhole() {
		final Collection<Expr<BoolType>> exprs = ExprSplitters.whole().apply(expr);
		Assert.assertEquals(1, exprs.size());
		Assert.assertEquals(expr, exprs.iterator().next());
	}

	@Test
	public void testConjuncts() {
		final Collection<Expr<BoolType>> exprs = ExprSplitters.conjuncts().apply(expr);
		Assert.assertEquals(2, exprs.size());
		Assert.assertTrue(exprs.contains(Not(x)));
		Assert.assertTrue(exprs.contains(Or(Not(y), z)));
	}

	@Test
	public void testAtoms() {
		final Collection<Expr<BoolType>> exprs = ExprSplitters.atoms().apply(expr);
		Assert.assertEquals(3, exprs.size());
		Assert.assertTrue(exprs.contains(x));
		Assert.assertTrue(exprs.contains(y));
		Assert.assertTrue(exprs.contains(z));
	}
}
