package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class AtomCollectorTests {

	@SuppressWarnings("serial")
	@Test
	public void test() {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();
		final ConstRefExpr<BoolType> ca = Const("a", Bool()).getRef();
		final ConstRefExpr<BoolType> cb = Const("b", Bool()).getRef();
		final ConstRefExpr<IntType> cx = Const("x", Int()).getRef();
		final ConstRefExpr<IntType> cy = Const("y", Int()).getRef();

		ExprUtils.collectAtoms(And(ca, Or(ca, Not(cb))), atoms);
		Assert.assertEquals(new HashSet<Expr<? extends Type>>() {
			{
				add(ca);
				add(cb);
			}
		}, atoms);

		atoms.clear();
		ExprUtils.collectAtoms(Imply(Eq(cx, Int(2)), Not(Leq(cx, cy))), atoms);
		Assert.assertEquals(new HashSet<Expr<? extends Type>>() {
			{
				add(Eq(cx, Int(2)));
				add(Leq(cx, cy));
			}
		}, atoms);
	}

}
