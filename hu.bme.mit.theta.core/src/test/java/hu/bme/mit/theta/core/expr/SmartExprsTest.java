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
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;

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

				{ True(), SmartBoolExprs.Not(False()) },

				{ False(), SmartBoolExprs.Not(True()) },

				{ A, SmartBoolExprs.Not(SmartBoolExprs.Not(A)) },

				{ Not(A), SmartBoolExprs.Not(SmartBoolExprs.Not(SmartBoolExprs.Not(A))) },

				{ True(), SmartBoolExprs.And(Collections.emptySet()) },

				{ A, SmartBoolExprs.And(Collections.singleton(A)) },

				{ A, SmartBoolExprs.And(A, True()) },

				{ A, SmartBoolExprs.And(A, True(), True()) },

				{ False(), SmartBoolExprs.And(A, False(), True()) },

				{ True(), SmartBoolExprs.And(True(), True()) },

				{ And(A, B, C), SmartBoolExprs.And(A, B, C, True()) },

				{ True(), SmartBoolExprs.Or(Collections.emptySet()) },

				{ A, SmartBoolExprs.Or(Collections.singleton(A)) },

				{ A, SmartBoolExprs.Or(A, False()) },

				{ A, SmartBoolExprs.Or(A, False(), False()) },

				{ True(), SmartBoolExprs.Or(A, False(), True()) },

				{ False(), SmartBoolExprs.Or(False(), False()) },

				{ Or(A, B, C), SmartBoolExprs.Or(A, B, C, False()) },

		});

	}

	@Test
	public void test() {
		Assert.assertEquals(expr, smartExpr);
	}
}
