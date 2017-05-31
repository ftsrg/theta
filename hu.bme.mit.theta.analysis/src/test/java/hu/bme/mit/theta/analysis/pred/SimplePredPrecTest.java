package hu.bme.mit.theta.analysis.pred;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;

import java.util.Collections;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class SimplePredPrecTest {

	private final VarDecl<IntType> x = Var("x", Int());
	private final VarDecl<IntType> y = Var("y", Int());

	private final Expr<BoolType> pred = Lt(x.getRef(), Int(5));

	private final Solver solver = Z3SolverFactory.getInstace().createSolver();

	@Test
	public void testMapping() {
		final PredPrec prec = SimplePredPrec.create(Collections.singleton(pred), solver);

		final PredState s1 = prec.createState(Valuation.builder().put(x, Int(0)).build());
		final PredState s2 = prec.createState(Valuation.builder().put(x, Int(10)).build());
		final PredState s3 = prec.createState(Valuation.builder().put(y, Int(0)).build());

		Assert.assertEquals(Collections.singleton(pred), s1.getPreds());
		Assert.assertEquals(Collections.singleton(Not(pred)), s2.getPreds());
		Assert.assertEquals(Collections.emptySet(), s3.getPreds());
	}

	@Test
	public void testRefinement() {
		final SimplePredPrec p0 = SimplePredPrec.create(solver);
		final SimplePredPrec p1 = SimplePredPrec.create(Collections.singleton(pred), solver);
		final SimplePredPrec p2 = SimplePredPrec.create(Collections.singleton(Exprs.Eq(x.getRef(), y.getRef())),
				solver);

		final SimplePredPrec r1 = p1.join(p0);
		final SimplePredPrec r2 = p1.join(p2);
		final SimplePredPrec r3 = p1.join(r2);

		Assert.assertTrue(p1 == r1);
		Assert.assertTrue(p1 != r2);
		Assert.assertTrue(r2 == r3);

	}

	@Test
	public void testEquals() {
		final SimplePredPrec p0 = SimplePredPrec.create(solver);
		final SimplePredPrec p1 = SimplePredPrec.create(Collections.singleton(pred), solver);
		final SimplePredPrec p2 = SimplePredPrec.create(Collections.singleton(pred), solver);

		Assert.assertNotEquals(p0, p1);
		Assert.assertNotEquals(p0, p2);
		Assert.assertEquals(p1, p2);
	}
}
