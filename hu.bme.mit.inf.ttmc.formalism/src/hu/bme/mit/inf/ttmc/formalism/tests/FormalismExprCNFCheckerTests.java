package hu.bme.mit.inf.ttmc.formalism.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;
import static hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils.isExprCNF;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public class FormalismExprCNFCheckerTests {

	// Constants and variaBles for testing
	private VarRefExpr<BoolType> vA, vB, vC;

	@Before
	public void Before() {
		// Create constants and variaBles
		vA = Var("A", Bool()).getRef();
		vB = Var("B", Bool()).getRef();
		vC = Var("C", Bool()).getRef();
	}

	@Test
	public void testCnfProgExprCheckerTrue() {
		// A
		assertTrue(isExprCNF(vA));
		// A'
		assertTrue(isExprCNF(Prime(vA)));
		// !A
		assertTrue(isExprCNF(Not(vA)));
		// !(A')
		assertTrue(isExprCNF(Not(Prime(vA))));
		// !A or B' or !C
		assertTrue(isExprCNF(Or(Not(vA), Prime(vB), Not(vC))));
		// !A and B' and !C
		assertTrue(isExprCNF(And(Not(vA), Prime(vB), Not(vC))));
		// !A and (B and !C)
		assertTrue(isExprCNF(And(Not(vA), And(vB, Not(vC)))));
		// !A and (B' or !C)
		assertTrue(isExprCNF(And(Not(vA), Or(Prime(vB), Not(vC)))));
	}

	@Test
	public void testCnfProgExprCheckerFalse() {
		// !!A
		assertFalse(isExprCNF(Not(Not(vA))));
		// !A and B and !C
		assertTrue(isExprCNF(And(Not(vA), vB, Not(vC))));
		// !A or (B and !C)
		assertFalse(isExprCNF(Or(Not(vA), And(vB, Not(vC)))));
		// !(A and B)
		assertFalse(isExprCNF(Not(And(vA, vB))));
		// !(A or B)
		assertFalse(isExprCNF(Not(Or(vA, vB))));
		// A -> B
		assertFalse(isExprCNF(Imply(vA, vB)));
		// A <-> B
		assertFalse(isExprCNF(Iff(vA, vB)));
		// (!A)'
		assertFalse(isExprCNF(Not(Not(vA))));
		// (A and B)'
		assertFalse(isExprCNF(Prime(And(vA, vB))));
		// (A or B)'
		assertFalse(isExprCNF(Prime(Or(vA, vB))));
	}
}
