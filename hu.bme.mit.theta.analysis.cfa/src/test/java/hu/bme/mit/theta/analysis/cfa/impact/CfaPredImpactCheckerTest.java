package hu.bme.mit.theta.analysis.cfa.impact;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Add;
import static hu.bme.mit.theta.core.expr.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.Exprs.False;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.expr.Exprs.Neq;
import static hu.bme.mit.theta.core.expr.Exprs.True;
import static hu.bme.mit.theta.core.stmt.Stmts.Assert;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Block;
import static hu.bme.mit.theta.core.stmt.Stmts.Do;
import static hu.bme.mit.theta.core.stmt.Stmts.If;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.impact.PredImpactChecker;
import hu.bme.mit.theta.analysis.cfa.CfaLts;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaCreator;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public final class CfaPredImpactCheckerTest {

	@Test
	public void test() {

		// Arrange
		final VarDecl<BoolType> vnondet = Var("nondet", Bool());
		final VarDecl<BoolType> vlock = Var("lock", Bool());
		final VarDecl<IntType> vold = Var("old", Int());
		final VarDecl<IntType> vnew = Var("new", Int());

		final Stmt program = Block(
				Assign(vlock,
						False()),
				Do(Block(Assert(Eq(vlock.getRef(), False())), Assign(vlock, True()), Assign(vold, vnew.getRef()),
						If(vnondet.getRef(), Block(Assign(vlock, False()), Assign(vnew, Add(vnew.getRef(), Int(1)))))),
						Neq(vnew.getRef(), vold.getRef())));

		final CFA cfa = CfaCreator.createSBE(program);

		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final PredImpactChecker<CfaLoc, CfaEdge> checker = PredImpactChecker.create(CfaLts.getInstance(),
				cfa.getInitLoc(), l -> l.equals(cfa.getErrorLoc()), solver);

		// Act
		final SafetyResult<? extends ExprState, ? extends ExprAction> status = checker
				.check(UnitPrec.getInstance());

		// Assert
		assertTrue(status.isSafe());

		final ARG<? extends ExprState, ? extends ExprAction> arg = status.getArg();
		arg.minimize();

		final ArgChecker argChecker = ArgChecker.create(solver);
		assertTrue(argChecker.isWellLabeled(arg));

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}
}
