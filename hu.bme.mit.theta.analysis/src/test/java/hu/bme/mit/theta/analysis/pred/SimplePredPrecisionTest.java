package hu.bme.mit.theta.analysis.pred;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SimplePredPrecisionTest {

	private final VarDecl<IntType> x = Decls.Var("x", Types.Int());
	private final VarDecl<IntType> y = Decls.Var("y", Types.Int());

	private final Expr<BoolType> pred = Exprs.Lt(x.getRef(), Exprs.Int(5));

	private final Solver solver = Z3SolverFactory.getInstace().createSolver();

	@Test
	public void testMapping() {
		final PredPrecision prec = SimplePredPrecision.create(Collections.singleton(pred), solver);

		final PredState s1 = prec.createState(Valuation.builder().put(x, Exprs.Int(0)).build());
		final PredState s2 = prec.createState(Valuation.builder().put(x, Exprs.Int(10)).build());
		final PredState s3 = prec.createState(Valuation.builder().put(y, Exprs.Int(0)).build());

		Assert.assertEquals(Collections.singleton(pred), s1.getPreds());
		Assert.assertEquals(Collections.singleton(Exprs.Not(pred)), s2.getPreds());
		Assert.assertEquals(Collections.emptySet(), s3.getPreds());
	}

	@Test
	public void testRefinement() {
		final SimplePredPrecision prec = SimplePredPrecision.create(Collections.singleton(pred), solver);

		final SimplePredPrecision refine1 = prec.refine(Exprs.True());
		final SimplePredPrecision refine2 = prec.refine(Exprs.False());
		final SimplePredPrecision refine3 = prec.refine(Exprs.Eq(x.getRef(), y.getRef()));

		Assert.assertTrue(prec == refine1);
		Assert.assertTrue(prec == refine2);
		Assert.assertTrue(prec != refine3);

	}
}
