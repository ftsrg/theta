package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.BoolType;

@RunWith(Parameterized.class)
public class SmartExprsTest {
	// Constants for testing
	private static final ConstRefExpr<BoolType> A = Const("a", Bool()).getRef();
	private static final ConstRefExpr<BoolType> B = Const("b", Bool()).getRef();
	private static final ConstRefExpr<BoolType> C = Const("c", Bool()).getRef();

	@Parameter(value = 0)
	public Expr<? extends BoolType> expr;

	@Parameter(value = 1)
	public Expr<? extends BoolType> smartExpr;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Exprs.True(), SmartExprs.Not(Exprs.False()) },

				{ Exprs.False(), SmartExprs.Not(Exprs.True()) },

				{ A, SmartExprs.Not(SmartExprs.Not(A)) },

				{ Exprs.Not(A), SmartExprs.Not(SmartExprs.Not(SmartExprs.Not(A))) },

				{ Exprs.True(), SmartExprs.And(Collections.emptySet()) },

				{ A, SmartExprs.And(Collections.singleton(A)) },

				{ A, SmartExprs.And(A, Exprs.True()) },

				{ A, SmartExprs.And(A, Exprs.True(), Exprs.True()) },

				{ Exprs.False(), SmartExprs.And(A, Exprs.False(), Exprs.True()) },

				{ Exprs.True(), SmartExprs.And(Exprs.True(), Exprs.True()) },

				{ Exprs.And(A, B, C), SmartExprs.And(A, B, C, Exprs.True()) },

				{ Exprs.True(), SmartExprs.Or(Collections.emptySet()) },

				{ A, SmartExprs.Or(Collections.singleton(A)) },

				{ A, SmartExprs.Or(A, Exprs.False()) },

				{ A, SmartExprs.Or(A, Exprs.False(), Exprs.False()) },

				{ Exprs.True(), SmartExprs.Or(A, Exprs.False(), Exprs.True()) },

				{ Exprs.False(), SmartExprs.Or(Exprs.False(), Exprs.False()) },

				{ Exprs.Or(A, B, C), SmartExprs.Or(A, B, C, Exprs.False()) },

		});

	}

	@Test
	public void test() {
		Assert.assertEquals(expr, smartExpr);
	}
}
