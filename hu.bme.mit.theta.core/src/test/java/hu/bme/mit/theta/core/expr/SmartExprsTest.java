package hu.bme.mit.theta.core.expr;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.type.booltype.BoolType;

@RunWith(Parameterized.class)
public class SmartExprsTest {
	// Constants for testing
	private static final Expr<BoolType> A = Const("a", Bool()).getRef();
	private static final Expr<BoolType> B = Const("b", Bool()).getRef();
	private static final Expr<BoolType> C = Const("c", Bool()).getRef();

	@Parameter(value = 0)
	public Expr<BoolType> expr;

	@Parameter(value = 1)
	public Expr<BoolType> smartExpr;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ True(), SmartExprs.Not(False()) },

				{ False(), SmartExprs.Not(True()) },

				{ A, SmartExprs.Not(SmartExprs.Not(A)) },

				{ Not(A), SmartExprs.Not(SmartExprs.Not(SmartExprs.Not(A))) },

				{ True(), SmartExprs.And(Collections.emptySet()) },

				{ A, SmartExprs.And(Collections.singleton(A)) },

				{ A, SmartExprs.And(A, True()) },

				{ A, SmartExprs.And(A, True(), True()) },

				{ False(), SmartExprs.And(A, False(), True()) },

				{ True(), SmartExprs.And(True(), True()) },

				{ And(A, B, C), SmartExprs.And(A, B, C, True()) },

				{ True(), SmartExprs.Or(Collections.emptySet()) },

				{ A, SmartExprs.Or(Collections.singleton(A)) },

				{ A, SmartExprs.Or(A, False()) },

				{ A, SmartExprs.Or(A, False(), False()) },

				{ True(), SmartExprs.Or(A, False(), True()) },

				{ False(), SmartExprs.Or(False(), False()) },

				{ Or(A, B, C), SmartExprs.Or(A, B, C, False()) },

		});

	}

	@Test
	public void test() {
		Assert.assertEquals(expr, smartExpr);
	}
}
