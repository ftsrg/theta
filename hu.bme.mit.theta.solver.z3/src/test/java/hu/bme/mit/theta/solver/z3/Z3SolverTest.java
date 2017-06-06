package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

public final class Z3SolverTest {

	@Test
	public void testTrack() {
		final Solver solver = Z3SolverFactory.getInstace().createSolver();

		final ConstDecl<BoolType> ca = Const("a", Bool());
		final Expr<BoolType> expr = And(ca.getRef(), True());

		solver.push();
		solver.track(expr);

		final SolverStatus status = solver.check();

		assertTrue(status.isSat());

		final Model model = solver.getModel();

		assertNotNull(model);

		solver.pop();
	}

}
