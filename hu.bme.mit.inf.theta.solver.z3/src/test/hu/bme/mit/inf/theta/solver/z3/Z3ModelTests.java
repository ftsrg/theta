package hu.bme.mit.inf.theta.solver.z3;

import org.junit.Test;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;

public class Z3ModelTests {

	static {
		new Z3SolverManager();
	}

	@Test
	public void test() {
		final Context context = new Context();
		final Solver solver = context.mkSimpleSolver();

		final BoolExpr a = context.mkBoolConst("a");
		final BoolExpr b = context.mkBoolConst("b");
		final BoolExpr expr = context.mkOr(a, b);

		solver.add(expr);
		solver.check();
		final Model model = solver.getModel();

		System.out.println(model.getConstInterp(a));
		System.out.println(model.getConstInterp(b));

		context.close();
	}
}
