package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Iff;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.isExprCNF;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

@RunWith(Parameterized.class)
public class CnfCheckerTest {
	// Constants for testing
	private static final ConstRefExpr<BoolType> a = Const("a", Bool()).getRef();
	private static final ConstRefExpr<BoolType> b = Const("b", Bool()).getRef();
	private static final ConstRefExpr<BoolType> c = Const("c", Bool()).getRef();

	@Parameter(value = 0)
	public Expr<? extends BoolType> expr;

	@Parameter(value = 1)
	public boolean expectedResult;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {
				// A
				{ a, true },
				// !A
				{ Not(a), true },
				// !A or B or !C
				{ Or(Not(a), b, Not(c)), true },
				// !A and B and !C
				{ And(Not(a), b, Not(c)), true },
				// !A and (B and !C)
				{ And(Not(a), And(b, Not(c))), true },
				// !A and (B or !C)
				{ And(Not(a), Or(b, Not(c))), true },
				// !!A
				{ Not(Not(a)), false },
				// !A and B and !C
				{ And(Not(a), b, Not(c)), true },
				// !A or (B and !C)
				{ Or(Not(a), And(b, Not(c))), false },
				// !(A and B)
				{ Not(And(a, b)), false },
				// !(A or B)
				{ Not(Or(a, b)), false },
				// A -> B
				{ Imply(a, b), false },
				// A <-> B
				{ Iff(a, b), false }, });

	}

	@Test
	public void test() {
		Assert.assertEquals(expectedResult, isExprCNF(expr));
	}
}
