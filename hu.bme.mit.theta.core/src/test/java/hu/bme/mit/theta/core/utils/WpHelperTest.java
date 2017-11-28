package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public final class WpHelperTest {

	private static final VarDecl<IntType> VX = Var("x", Int());
	private static final VarDecl<IntType> VY = Var("y", Int());

	private static final Expr<IntType> X = VX.getRef();
	private static final Expr<IntType> Y = VY.getRef();

	private static final Expr<BoolType> TRUE = True();
	private static final Expr<BoolType> GEQ_X_1 = Geq(X, Int(1));
	private static final Expr<BoolType> GEQ_1_X = Geq(Int(1), X);
	private static final Expr<BoolType> GEQ_1_Y = Geq(Int(1), Y);
	private static final Expr<BoolType> GEQ_X_Y = Geq(X, Y);

	private static final Stmt ASSIGN_X_1 = Assign(VX, Int(1));
	private static final Stmt ASSIGN_Y_X = Assign(VY, X);

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ TRUE, ASSIGN_X_1, TRUE },

				{ GEQ_X_1, ASSIGN_X_1, TRUE },

				{ GEQ_1_X, ASSIGN_X_1, TRUE },

				{ GEQ_1_Y, ASSIGN_X_1, GEQ_1_Y },

				{ GEQ_X_Y, ASSIGN_X_1, GEQ_1_Y },

				{ TRUE, ASSIGN_Y_X, TRUE },

				{ GEQ_X_1, ASSIGN_Y_X, GEQ_X_1 },

				{ GEQ_1_X, ASSIGN_Y_X, GEQ_1_X },

				{ GEQ_1_Y, ASSIGN_Y_X, GEQ_1_X },

				{ GEQ_X_Y, ASSIGN_Y_X, TRUE },

		});
	}

	@Parameter(0)
	public Expr<BoolType> expr;

	@Parameter(1)
	public Stmt stmt;

	@Parameter(2)
	public Expr<BoolType> expectedWp;

	@Test
	public void test() {
		// Arrange
		final WpState state = WpState.of(expr, 0);

		// Act
		final WpState actualState = WpHelper.wp(stmt, state);
		final Expr<BoolType> actualWp = ExprUtils.simplify(actualState.getExpr());

		// Assert
		assertEquals(expectedWp, actualWp);
	}

}
