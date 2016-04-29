package hu.bme.mit.inf.ttmc.core.tests;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ref;
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
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;

public class AtomCollectorTests {

	@Test
	public void test() {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();
		final ConstRefExpr<BoolType> ca = Ref(Const("a", Bool()));
		final ConstRefExpr<BoolType> cb = Ref(Const("b", Bool()));
		final ConstRefExpr<IntType> cx = Ref(Const("x", Int()));
		final ConstRefExpr<IntType> cy = Ref(Const("y", Int()));

		ExprUtils.collectAtoms(And(ca, Or(ca, Not(cb))), atoms);
		Assert.assertEquals(of(ca, cb), atoms);

		atoms.clear();
		ExprUtils.collectAtoms(Imply(Eq(cx, Int(2)), Not(Leq(cx, cy))), atoms);
		Assert.assertEquals(of(Eq(cx, Int(2)), Leq(cx, cy)), atoms);
	}

}
