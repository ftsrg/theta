package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

@RunWith(Parameterized.class)
public class AtomCollectorTest {

	private static final ConstRefExpr<BoolType> ca = Const("a", Bool()).getRef();
	private static final ConstRefExpr<BoolType> cb = Const("b", Bool()).getRef();
	private static final ConstRefExpr<IntType> cx = Const("x", Int()).getRef();
	private static final ConstRefExpr<IntType> cy = Const("y", Int()).getRef();

	@Parameter(value = 0)
	public Expr<? extends BoolType> expr;

	@Parameter(value = 1)
	public Set<Expr<? extends BoolType>> expectedAtoms;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ And(ca, Or(ca, Not(cb))), of(ca, cb) },

				{ Imply(Eq(cx, Int(2)), Not(Leq(cx, cy))), of(Eq(cx, Int(2)), Leq(cx, cy)) },

				{ Iff(And(Leq(cx, cy), Eq(cx, cy)), Or(Not(Leq(cx, cy)), ca)), of(ca, Leq(cx, cy), Eq(cx, cy)) },

				{ And(Ite(ca, ca, cb), Not(ca)), of(ca, Ite(ca, ca, cb)) },

		});
	}

	@Test
	public void test() {
		final Set<Expr<? extends BoolType>> atoms = new HashSet<>();

		ExprUtils.collectAtoms(expr, atoms);
		Assert.assertEquals(expectedAtoms, atoms);

	}

}
