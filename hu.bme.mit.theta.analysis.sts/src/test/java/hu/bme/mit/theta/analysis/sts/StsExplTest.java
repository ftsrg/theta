package hu.bme.mit.theta.analysis.sts;

import static hu.bme.mit.theta.analysis.algorithm.ArgUtils.isWellLabeled;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Prime;
import static hu.bme.mit.theta.core.type.Types.Int;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.VarsRefutation;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.ConsoleLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.STS.Builder;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class StsExplTest {

	@Test
	public void test() {

		final Logger logger = new ConsoleLogger(100);

		final VarDecl<IntType> vx = Var("x", Int());
		final Expr<IntType> x = vx.getRef();
		final VarDecl<IntType> vy = Var("y", Int());
		final Expr<IntType> y = vy.getRef();

		final int mod = 10;

		final Builder builder = STS.builder();

		builder.addInit(Eq(x, Int(0)));
		builder.addInit(Eq(y, Int(0)));
		builder.addTrans(And(Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))),
				Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
		builder.addTrans(Eq(Prime(y), Int(0)));
		builder.setProp(Not(Eq(x, Int(mod))));

		final STS sts = builder.build();

		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final Analysis<ExplState, ExprAction, ExplPrec> analysis = ExplAnalysis.create(solver, sts.getInit());
		final Predicate<ExprState> target = new ExprStatePredicate(Not(sts.getProp()), solver);

		final ExplPrec prec = ExplPrec.create(Collections.singleton(vy));

		final LTS<State, StsAction> lts = StsLts.create(sts);

		final ArgBuilder<ExplState, StsAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis, target);

		final Abstractor<ExplState, StsAction, ExplPrec> abstractor = WaitlistBasedAbstractor.create(argBuilder,
				PriorityWaitlist.supplier(ArgNodeComparators.bfs()), logger);

		final ExprTraceChecker<VarsRefutation> exprTraceChecker = ExprTraceUnsatCoreChecker.create(sts.getInit(),
				Not(sts.getProp()), solver);

		final SingleExprTraceRefiner<ExplState, StsAction, ExplPrec, VarsRefutation> refiner = SingleExprTraceRefiner
				.create(exprTraceChecker, JoiningPrecRefiner.create(new VarsRefToExplPrec()), logger);

		final SafetyChecker<ExplState, StsAction, ExplPrec> checker = CegarChecker.create(abstractor, refiner, logger);

		final SafetyResult<ExplState, StsAction> safetyStatus = checker.check(prec);

		final ARG<ExplState, StsAction> arg = safetyStatus.getArg();
		assertTrue(isWellLabeled(arg, solver));

		// System.out.println(new
		// GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
