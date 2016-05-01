package hu.bme.mit.inf.ttmc.core.tests;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils.isExprCNF;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

public class ExprCNFCheckerTests {
	// Constants for testing
	private ConstRefExpr<BoolType> a, b, c;

	@Before
	public void before() {
		// Create constants
		a = Const("a", Bool()).getRef();
		b = Const("b", Bool()).getRef();
		c = Const("c", Bool()).getRef();
	}

	@Test
	public void testCnfCheckerTrue() {
		// A
		assertTrue(isExprCNF(a));
		// !A
		assertTrue(isExprCNF(Not(a)));
		// !A or B or !C
		assertTrue(isExprCNF(Or(Not(a), b, Not(c))));
		// !A and B and !C
		assertTrue(isExprCNF(And(Not(a), b, Not(c))));
		// !A and (B and !C)
		assertTrue(isExprCNF(And(Not(a), And(b, Not(c)))));
		// !A and (B or !C)
		assertTrue(isExprCNF(And(Not(a), Or(b, Not(c)))));
	}

	@Test
	public void testCnfCheckerFalse() {
		// !!A
		assertFalse(isExprCNF(Not(Not(a))));
		// !A and B and !C
		assertTrue(isExprCNF(And(Not(a), b, Not(c))));
		// !A or (B and !C)
		assertFalse(isExprCNF(Or(Not(a), And(b, Not(c)))));
		// !(A and B)
		assertFalse(isExprCNF(Not(And(a, b))));
		// !(A or B)
		assertFalse(isExprCNF(Not(Or(a, b))));
		// A -> B
		assertFalse(isExprCNF(Imply(a, b)));
		// A <-> B
		assertFalse(isExprCNF(Iff(a, b)));
	}
}
