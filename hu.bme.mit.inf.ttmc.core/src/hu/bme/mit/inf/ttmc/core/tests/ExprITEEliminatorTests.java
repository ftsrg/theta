package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neg;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils.eliminateITE;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;

public class ExprITEEliminatorTests {

	// Constants for testing
	private ConstRefExpr<BoolType> cA, cB, cC, cD, cE;
	private ConstRefExpr<IntType> cX, cY, cZ, cT;
	private IntLitExpr i1, i2, i3, i4, i5;

	@Before
	public void before() {

		// Create constants
		cA = Const("A", Bool()).getRef();
		cB = Const("B", Bool()).getRef();
		cC = Const("C", Bool()).getRef();
		cD = Const("D", Bool()).getRef();
		cE = Const("E", Bool()).getRef();
		cX = Const("X", Int()).getRef();
		cY = Const("Y", Int()).getRef();
		cZ = Const("Z", Int()).getRef();
		cT = Const("T", Int()).getRef();
		i1 = Int(1);
		i2 = Int(2);
		i3 = Int(3);
		i4 = Int(4);
		i5 = Int(5);
	}

	@Test
	public void testSimple() {
		// if A then B else C
		assertEquals(eliminateITE(Ite(cA, cB, cC)), And(Or(Not(cA), cB), Or(cA, cC)));

		// if A then (if B then C else D) else E
		assertEquals(eliminateITE(Ite(cA, Ite(cB, cC, cD), cE)), And(Or(Not(cA), And(Or(Not(cB), cC), Or(cB, cD))), Or(cA, cE)));
	}

	@Test
	public void testUnary() {
		// !(if A then B else C)
		assertEquals(eliminateITE(Not(Ite(cA, cB, cC))), Not(And(Or(Not(cA), cB), Or(cA, cC))));
	}

	@Test
	public void testBinary() {
		// A -> (if B then C else D)
		assertEquals(eliminateITE(Imply(cA, Ite(cB, cC, cD))), Imply(cA, And(Or(Not(cB), cC), Or(cB, cD))));
		// (if B then C else D) -> A
		assertEquals(eliminateITE(Imply(Ite(cB, cC, cD), cA)), Imply(And(Or(Not(cB), cC), Or(cB, cD)), cA));
		// A = (if B then C else D)
		assertEquals(eliminateITE(Eq(cA, Ite(cB, cC, cD))), Eq(cA, And(Or(Not(cB), cC), Or(cB, cD))));
		// X = (if A then Y else Z)
		assertEquals(eliminateITE(Eq(cX, Ite(cA, cY, cZ))), And(Or(Not(cA), Eq(cX, cY)), Or(cA, Eq(cX, cZ))));
		// (if A then Y else Z) = X
		assertEquals(eliminateITE(Eq(Ite(cA, cY, cZ), cX)), And(Or(Not(cA), Eq(cY, cX)), Or(cA, Eq(cZ, cX))));
		// X = (if A then (if B then Y else Z) else T)
		assertEquals(eliminateITE(Eq(cX, Ite(cA, Ite(cB, cY, cZ), cT))),
				And(Or(Not(cA), And(Or(Not(cB), Eq(cX, cY)), Or(cB, Eq(cX, cZ)))), Or(cA, Eq(cX, cT))));
		// (if A then (if B then Y else Z) else T) = X
		assertEquals(eliminateITE(Eq(Ite(cA, Ite(cB, cY, cZ), cT), cX)),
				And(Or(Not(cA), And(Or(Not(cB), Eq(cY, cX)), Or(cB, Eq(cZ, cX)))), Or(cA, Eq(cT, cX))));
		// (if A then X else Y) = (if B then Z else T)
		assertEquals(eliminateITE(Eq(Ite(cA, cX, cY), Ite(cB, cZ, cT))),
				And(Or(Not(cA), And(Or(Not(cB), Eq(cX, cZ)), Or(cB, Eq(cX, cT)))), Or(cA, And(Or(Not(cB), Eq(cY, cZ)), Or(cB, Eq(cY, cT))))));
	}

	@Test
	public void testMultiary() {
		// A or B or (if C then D else E)
		assertEquals(eliminateITE(Or(cA, cB, Ite(cC, cD, cE))), Or(cA, cB, And(Or(Not(cC), cD), Or(cC, cE))));
		// 1 = 2 + (if A then 3 else 4) + 5
		assertEquals(eliminateITE(Eq(i1, Add(i2, Ite(cA, i3, i4), i5))), And(Or(Not(cA), Eq(i1, Add(i2, i3, i5))), Or(cA, Eq(i1, Add(i2, i4, i5)))));
		// 1 = 2 + (if A then 3 else 4) + (if B then X else Y)
		assertEquals(eliminateITE(Eq(i1, Add(i2, Ite(cA, i3, i4), Ite(cB, cX, cY)))),
				And(Or(Not(cA), And(Or(Not(cB), Eq(i1, Add(i2, i3, cX))), Or(cB, Eq(i1, Add(i2, i3, cY))))),
						Or(cA, And(Or(Not(cB), Eq(i1, Add(i2, i4, cX))), Or(cB, Eq(i1, Add(i2, i4, cY)))))));
	}

	@Test
	public void testNothingHappening() {
		final List<Expr<? extends BoolType>> expressions = new ArrayList<>();
		expressions.add(And(cA, cB, cD));
		expressions.add(Eq(cX, Neg(cY)));
		expressions.add(Geq(Sub(cX, cY), Add(cX, cZ, cT)));

		for (final Expr<? extends BoolType> expr : expressions)
			assertEquals(expr, eliminateITE(expr));
	}
}
