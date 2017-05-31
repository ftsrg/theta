package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.isExprCNF;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

@RunWith(Parameterized.class)
public class CnfCheckerTest {
	// Constants for testing
	private static final Expr<BoolType> A = Const("a", Bool()).getRef();
	private static final Expr<BoolType> B = Const("b", Bool()).getRef();
	private static final Expr<BoolType> C = Const("c", Bool()).getRef();

	@Parameter(value = 0)
	public Expr<? extends BoolType> expr;

	@Parameter(value = 1)
	public boolean expectedResult;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {
				// A
				{ A, true },
				// !A
				{ Not(A), true },
				// !A or B or !C
				{ Or(Not(A), B, Not(C)), true },
				// !A and B and !C
				{ And(Not(A), B, Not(C)), true },
				// !A and (B and !C)
				{ And(Not(A), And(B, Not(C))), true },
				// !A and (B or !C)
				{ And(Not(A), Or(B, Not(C))), true },
				// !!A
				{ Not(Not(A)), false },
				// !A and B and !C
				{ And(Not(A), B, Not(C)), true },
				// !A or (B and !C)
				{ Or(Not(A), And(B, Not(C))), false },
				// !(A and B)
				{ Not(And(A, B)), false },
				// !(A or B)
				{ Not(Or(A, B)), false },
				// A -> B
				{ Imply(A, B), false },
				// A <-> B
				{ Iff(A, B), false }, });

	}

	@Test
	public void test() {
		Assert.assertEquals(expectedResult, isExprCNF(expr));
	}
}
