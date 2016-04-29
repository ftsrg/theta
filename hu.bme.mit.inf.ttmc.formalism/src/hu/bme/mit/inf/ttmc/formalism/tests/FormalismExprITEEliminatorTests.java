package hu.bme.mit.inf.ttmc.formalism.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;
import static hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils.eliminate;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public class FormalismExprITEEliminatorTests {

	// Constants and variables for testing
	private VarRefExpr<BoolType> vA;
	private VarRefExpr<IntType> vB, vC, vD;

	@Before
	public void before() {
		// Create constants and variables
		vA = Ref(Var("A", Bool()));
		vB = Ref(Var("B", Int()));
		vC = Ref(Var("C", Int()));
		vD = Ref(Var("D", Int()));
	}

	@Test
	public void testProgExprIteEliminator() {
		// D = if A then B else C
		assertEquals(eliminate(Eq(vD, Ite(vA, vB, vC))), And(Or(Not(vA), Eq(vD, vB)), Or(vA, Eq(vD, vC))));
		// D = (if A then B else C)'
		assertEquals(eliminate(Eq(vD, Prime(Ite(vA, vB, vC)))),
				And(Or(Not(vA), Eq(vD, Prime(vB))), Or(vA, Eq(vD, Prime(vC)))));
	}
}
