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
	private ConstRefExpr<BoolType> cA, cB, cC;

	@Before
	public void before() {
		// Create constants
		cA = Const("A", Bool()).getRef();
		cB = Const("B", Bool()).getRef();
		cC = Const("C", Bool()).getRef();
	}

	@Test
	public void testCnfCheckerTrue() {
		// A
		assertTrue(isExprCNF(cA));
		// !A
		assertTrue(isExprCNF(Not(cA)));
		// !A or B or !C
		assertTrue(isExprCNF(Or(Not(cA), cB, Not(cC))));
		// !A and B and !C
		assertTrue(isExprCNF(And(Not(cA), cB, Not(cC))));
		// !A and (B and !C)
		assertTrue(isExprCNF(And(Not(cA), And(cB, Not(cC)))));
		// !A and (B or !C)
		assertTrue(isExprCNF(And(Not(cA), Or(cB, Not(cC)))));
	}

	@Test
	public void testCnfCheckerFalse() {
		// !!A
		assertFalse(isExprCNF(Not(Not(cA))));
		// !A and B and !C
		assertTrue(isExprCNF(And(Not(cA), cB, Not(cC))));
		// !A or (B and !C)
		assertFalse(isExprCNF(Or(Not(cA), And(cB, Not(cC)))));
		// !(A and B)
		assertFalse(isExprCNF(Not(And(cA, cB))));
		// !(A or B)
		assertFalse(isExprCNF(Not(Or(cA, cB))));
		// A -> B
		assertFalse(isExprCNF(Imply(cA, cB)));
		// A <-> B
		assertFalse(isExprCNF(Iff(cA, cB)));
	}
}
