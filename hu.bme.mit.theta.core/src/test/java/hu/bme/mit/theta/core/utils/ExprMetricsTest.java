package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Add;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Sub;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprMetrics;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

@RunWith(Parameterized.class)
public class ExprMetricsTest {

	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<IntType> VB = Var("b", Int());

	private static final Expr<BoolType> A = VA.getRef();
	private static final Expr<IntType> B = VB.getRef();

	@Parameter(value = 0)
	public Expr<? extends Type> expr;

	@Parameter(value = 1)
	public ExprMetrics.ExprMetric metric;

	@Parameter(value = 2)
	public int expectedSize;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ True(), ExprMetrics.absoluteSize(), 1 },

				{ A, ExprMetrics.absoluteSize(), 1 },

				{ And(A, True()), ExprMetrics.absoluteSize(), 3 },

				{ And(A, True(), False()), ExprMetrics.absoluteSize(), 5 },

				{ And(A, And(True(), False())), ExprMetrics.absoluteSize(), 5 },

				{ Add(B, Sub(Int(1), Int(2)), Int(3)), ExprMetrics.absoluteSize(), 7 },

		});
	}

	@Test
	public void test() {
		final int actualSize = ExprUtils.size(expr, metric);
		assertEquals(expectedSize, actualSize);
	}
}
