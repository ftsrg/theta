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
import static hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils.eliminate;
import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;

public class FormalismExprITEEliminatorTests {

	// Constants and variables for testing
	private VarRefExpr<BoolType> a;
	private VarRefExpr<IntType> b, c, d;

	@Before
	public void before() {
		// Create constants and variables
		a = Var("a", Bool()).getRef();
		b = Var("b", Int()).getRef();
		c = Var("c", Int()).getRef();
		d = Var("d", Int()).getRef();
	}

	@Test
	public void testProgExprIteEliminator() {
		// D = if A then B else C
		assertEquals(eliminate(Eq(d, Ite(a, b, c))), And(Or(Not(a), Eq(d, b)), Or(a, Eq(d, c))));
		// D = (if A then B else C)'
		assertEquals(eliminate(Eq(d, Prime(Ite(a, b, c)))), And(Or(Not(a), Eq(d, Prime(b))), Or(a, Eq(d, Prime(c)))));
	}
}
