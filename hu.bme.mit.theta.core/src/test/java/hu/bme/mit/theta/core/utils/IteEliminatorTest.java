package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.eliminateITE;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;

public class IteEliminatorTest {

	// Constants for testing
	private ConstRefExpr<BoolType> a, b, c, d, e;
	private ConstRefExpr<IntType> x, y, z, t;
	private IntLitExpr i1, i2, i3, i4, i5;

	@Before
	public void before() {

		// Create constants
		a = Const("a", Bool()).getRef();
		b = Const("b", Bool()).getRef();
		c = Const("c", Bool()).getRef();
		d = Const("d", Bool()).getRef();
		e = Const("e", Bool()).getRef();
		x = Const("x", Int()).getRef();
		y = Const("y", Int()).getRef();
		z = Const("z", Int()).getRef();
		t = Const("t", Int()).getRef();
		i1 = Int(1);
		i2 = Int(2);
		i3 = Int(3);
		i4 = Int(4);
		i5 = Int(5);
	}

	@Test
	public void testSimple() {
		// if A then B else C
		assertEquals(eliminateITE(Ite(a, b, c)), And(Or(Not(a), b), Or(a, c)));

		// if A then (if B then C else D) else E
		assertEquals(eliminateITE(Ite(a, Ite(b, c, d), e)), And(Or(Not(a), And(Or(Not(b), c), Or(b, d))), Or(a, e)));
	}

	@Test
	public void testUnary() {
		// !(if A then B else C)
		assertEquals(eliminateITE(Not(Ite(a, b, c))), Not(And(Or(Not(a), b), Or(a, c))));
	}

	@Test
	public void testBinary() {
		// A -> (if B then C else D)
		assertEquals(eliminateITE(Imply(a, Ite(b, c, d))), Imply(a, And(Or(Not(b), c), Or(b, d))));
		// (if B then C else D) -> A
		assertEquals(eliminateITE(Imply(Ite(b, c, d), a)), Imply(And(Or(Not(b), c), Or(b, d)), a));
		// A = (if B then C else D)
		assertEquals(eliminateITE(Eq(a, Ite(b, c, d))), Eq(a, And(Or(Not(b), c), Or(b, d))));
		// X = (if A then Y else Z)
		assertEquals(eliminateITE(Eq(x, Ite(a, y, z))), And(Or(Not(a), Eq(x, y)), Or(a, Eq(x, z))));
		// (if A then Y else Z) = X
		assertEquals(eliminateITE(Eq(Ite(a, y, z), x)), And(Or(Not(a), Eq(y, x)), Or(a, Eq(z, x))));
		// X = (if A then (if B then Y else Z) else T)
		assertEquals(eliminateITE(Eq(x, Ite(a, Ite(b, y, z), t))),
				And(Or(Not(a), And(Or(Not(b), Eq(x, y)), Or(b, Eq(x, z)))), Or(a, Eq(x, t))));
		// (if A then (if B then Y else Z) else T) = X
		assertEquals(eliminateITE(Eq(Ite(a, Ite(b, y, z), t), x)),
				And(Or(Not(a), And(Or(Not(b), Eq(y, x)), Or(b, Eq(z, x)))), Or(a, Eq(t, x))));
		// (if A then X else Y) = (if B then Z else T)
		assertEquals(eliminateITE(Eq(Ite(a, x, y), Ite(b, z, t))),
				And(Or(Not(a), And(Or(Not(b), Eq(x, z)), Or(b, Eq(x, t)))),
						Or(a, And(Or(Not(b), Eq(y, z)), Or(b, Eq(y, t))))));
	}

	@Test
	public void testMultiary() {
		// A or B or (if C then D else E)
		assertEquals(eliminateITE(Or(a, b, Ite(c, d, e))), Or(a, b, And(Or(Not(c), d), Or(c, e))));
		// 1 = 2 + (if A then 3 else 4) + 5
		assertEquals(eliminateITE(Eq(i1, Add(i2, Ite(a, i3, i4), i5))),
				And(Or(Not(a), Eq(i1, Add(i2, i3, i5))), Or(a, Eq(i1, Add(i2, i4, i5)))));
		// 1 = 2 + (if A then 3 else 4) + (if B then X else Y)
		assertEquals(eliminateITE(Eq(i1, Add(i2, Ite(a, i3, i4), Ite(b, x, y)))),
				And(Or(Not(a), And(Or(Not(b), Eq(i1, Add(i2, i3, x))), Or(b, Eq(i1, Add(i2, i3, y))))),
						Or(a, And(Or(Not(b), Eq(i1, Add(i2, i4, x))), Or(b, Eq(i1, Add(i2, i4, y)))))));
	}

	@Test
	public void testNothingHappening() {
		final List<Expr<? extends BoolType>> expressions = new ArrayList<>();
		expressions.add(And(a, b, d));
		expressions.add(Eq(x, Neg(y)));
		expressions.add(Geq(Sub(x, y), Add(x, z, t)));

		for (final Expr<? extends BoolType> expr : expressions)
			assertEquals(expr, eliminateITE(expr));
	}

	@Test
	public void testPrime() {
		// D = (if A then X else Y)'
		assertEquals(eliminateITE(Eq(z, Prime(Ite(a, x, y)))),
				And(Or(Not(a), Eq(z, Prime(x))), Or(a, Eq(z, Prime(y)))));
	}
}
