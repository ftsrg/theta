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
import static hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils.eliminate;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSManagerImpl;

public class FormalismExprITEEliminatorTests {
	// Manager and factories
	STSManager manager;

	// Constants and variables for testing
	private VarRefExpr<BoolType> vA;
	private VarRefExpr<IntType> vB, vC, vD;

	@Before
	public void before() {
		// Create manager
		manager = new STSManagerImpl();

		// Create constants and variables
		vA = Var("A", Bool()).getRef();
		vB = Var("B", Int()).getRef();
		vC = Var("C", Int()).getRef();
		vD = Var("D", Int()).getRef();
	}

	@Test
	public void testProgExprIteEliminator() {
		// D = if A then B else C
		assertEquals(eliminate(Eq(vD, Ite(vA, vB, vC)), manager), And(Or(Not(vA), Eq(vD, vB)), Or(vA, Eq(vD, vC))));
		// D = (if A then B else C)'
		assertEquals(eliminate(Eq(vD, Prime(Ite(vA, vB, vC))), manager),
				And(Or(Not(vA), Eq(vD, Prime(vB))), Or(vA, Eq(vD, Prime(vC)))));
	}
}
