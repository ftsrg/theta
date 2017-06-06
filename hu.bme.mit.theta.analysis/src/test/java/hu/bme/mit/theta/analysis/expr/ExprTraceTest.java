package hu.bme.mit.theta.analysis.expr;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class ExprTraceTest {

	@Test
	public void testFeasable() {
		// Arrange
		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final Expr<IntType> x = Var("x", Int()).getRef();
		final Expr<BoolType> trans = Eq(Prime(x), Add(x, Int(1)));

		final ExprAction actionMock = mock(ExprAction.class);
		doReturn(trans).when(actionMock).toExpr();
		when(actionMock.nextIndexing()).thenReturn(VarIndexing.all(1));

		final List<ExprAction> actions = Arrays.asList(actionMock, actionMock, actionMock);
		final Trace<ExprState, ExprAction> trace = ExprTraceUtils.traceFrom(actions);

		final ExprTraceChecker<?> traceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);

		// Act
		final ExprTraceStatus<?> status = traceChecker.check(trace);

		// Assert
		assertTrue(status.isFeasible());
		System.out.println(status.asFeasible().getValuations());
	}

	@Test
	public void testUnfeasable() {
		// Arrange
		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final Expr<IntType> x = Var("x", Int()).getRef();
		final Expr<BoolType> trans1 = Eq(Prime(x), Int(0));
		final Expr<BoolType> trans2 = Geq(x, Int(1));

		final ExprAction action1Mock = mock(ExprAction.class);
		doReturn(trans1).when(action1Mock).toExpr();
		when(action1Mock.nextIndexing()).thenReturn(VarIndexing.all(1));

		final ExprAction action2Mock = mock(ExprAction.class);
		doReturn(trans2).when(action2Mock).toExpr();
		when(action2Mock.nextIndexing()).thenReturn(VarIndexing.all(0));

		final List<ExprAction> actions = Arrays.asList(action1Mock, action2Mock);
		final Trace<ExprState, ExprAction> trace = ExprTraceUtils.traceFrom(actions);

		final ExprTraceChecker<ItpRefutation> traceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);

		// Act
		final ExprTraceStatus<ItpRefutation> status = traceChecker.check(trace);

		// Assert
		assertTrue(status.isInfeasible());
		System.out.println(status.asInfeasible().getRefutation());
	}

}
