package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.kframework.mpfr.BigFloat;

import java.util.Collection;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.Abs;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.IsNan;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class Z3SolverFPTest {
	@Parameterized.Parameter(0)
	public Class<?> exprType;

	@Parameterized.Parameter(1)
	public Expr<?> expected;

	@Parameterized.Parameter(2)
	public Expr<?> actual;

	@Parameters(name = "expr: {0}, expected: {1}, actual: {2}")
	public static Collection<?> operations() {
		return FpTestUtils.GetOperations().collect(Collectors.toUnmodifiableList());
	}

	@Test
	public void testOperationEquals() {
		// Sanity check
		assertNotNull(exprType);
		assertNotNull(expected);
		assertNotNull(actual);

		// Type checks
		assertTrue(
				"The type of actual is " + actual.getClass().getName() + " instead of " + exprType.getName(),
				exprType.isInstance(actual)
		);
		assertEquals(
				"The type of expected (" + expected.getType() + ") must match the type of actual (" + actual.getType() + ")",
				expected.getType(),
				actual.getType()
		);

		// Equality check
		final Solver solver = Z3SolverFactory.getInstance().createSolver();
		solver.push();


		if (expected instanceof FpLitExpr && actual.getType() instanceof FpType) {
			if (((FpLitExpr) expected).isNaN()) {
				//noinspection unchecked
				solver.add(IsNan((Expr<FpType>) actual));
			} else if (((FpLitExpr) expected).isNegativeInfinity()) {
				solver.add(EqExpr.create2(expected, actual));
			} else if (((FpLitExpr) expected).isPositiveInfinity()) {
				solver.add(EqExpr.create2(expected, actual));
			} else {
				//noinspection unchecked
				FpLeqExpr leq = Leq(Abs(Sub(RNE, (FpLitExpr) expected, (Expr<FpType>) actual)),
						FpUtils.bigFloatToFpLitExpr(new BigFloat("1e-2", FpUtils.getMathContext((FpType) actual.getType(), RNE)), (FpType) actual.getType()));
				solver.add(leq);
			}
		} else {
			solver.add(EqExpr.create2(expected, actual));
		}
		SolverStatus status = solver.check();
		assertTrue(status.isSat());
	}
}
