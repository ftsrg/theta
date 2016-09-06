package hu.bme.mit.inf.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.inf.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;

import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils;

public class AtomCollectorTests {

	@Test
	public void test() {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();
		final ConstRefExpr<BoolType> ca = Const("a", Bool()).getRef();
		final ConstRefExpr<BoolType> cb = Const("b", Bool()).getRef();
		final ConstRefExpr<IntType> cx = Const("x", Int()).getRef();
		final ConstRefExpr<IntType> cy = Const("y", Int()).getRef();

		ExprUtils.collectAtoms(And(ca, Or(ca, Not(cb))), atoms);
		Assert.assertEquals(of(ca, cb), atoms);

		atoms.clear();
		ExprUtils.collectAtoms(Imply(Eq(cx, Int(2)), Not(Leq(cx, cy))), atoms);
		Assert.assertEquals(of(Eq(cx, Int(2)), Leq(cx, cy)), atoms);
	}

}
