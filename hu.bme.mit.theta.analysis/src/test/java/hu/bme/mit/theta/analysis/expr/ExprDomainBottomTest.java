package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

@RunWith(Parameterized.class)
public final class ExprDomainBottomTest {

	private static final Expr<IntType> X;

	static {
		final VarDecl<IntType> vx = Var("x", Int());
		X = vx.getRef();
	}

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ PredState.create(False()), true },

				{ PredState.create(And(Leq(X, Int(0)), Geq(X, Int(1)))), true },

				{ PredState.create(Geq(X, Int(0))), false },

				{ PredState.create(), false },

				{ PredState.create(True()), false }

		});
	}

	@Parameter(value = 0)
	public ExprState state;

	@Parameter(value = 1)
	public boolean bottom;

	@Test
	public void testIsBottom() {
		final Solver solver = new Z3SolverManager().createSolver(true, true);
		final Domain<ExprState> domain = ExprDomain.create(solver);
		assertEquals(domain.isBottom(state), bottom);
	}

}
