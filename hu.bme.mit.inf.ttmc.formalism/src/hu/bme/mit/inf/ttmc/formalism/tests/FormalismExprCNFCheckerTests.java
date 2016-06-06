package hu.bme.mit.inf.ttmc.formalism.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;
import static hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils.isExprCNF;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public class FormalismExprCNFCheckerTests {

	// Constants and variaBles for testing
	private VarRefExpr<BoolType> a, b, c;

	@Before
	public void Before() {
		// Create constants and variaBles
		a = Var("a", Bool()).getRef();
		b = Var("b", Bool()).getRef();
		c = Var("c", Bool()).getRef();
	}

	@Test
	public void testCnfProgExprCheckerTrue() {
		// A
		assertTrue(isExprCNF(a));
		// A'
		assertTrue(isExprCNF(Prime(a)));
		// !A
		assertTrue(isExprCNF(Not(a)));
		// !(A')
		assertTrue(isExprCNF(Not(Prime(a))));
		// !A or B' or !C
		assertTrue(isExprCNF(Or(Not(a), Prime(b), Not(c))));
		// !A and B' and !C
		assertTrue(isExprCNF(And(Not(a), Prime(b), Not(c))));
		// !A and (B and !C)
		assertTrue(isExprCNF(And(Not(a), And(b, Not(c)))));
		// !A and (B' or !C)
		assertTrue(isExprCNF(And(Not(a), Or(Prime(b), Not(c)))));
	}

	@Test
	public void testCnfProgExprCheckerFalse() {
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
		// (!A)'
		assertFalse(isExprCNF(Not(Not(a))));
		// (A and B)'
		assertFalse(isExprCNF(Prime(And(a, b))));
		// (A or B)'
		assertFalse(isExprCNF(Prime(Or(a, b))));
	}
}
