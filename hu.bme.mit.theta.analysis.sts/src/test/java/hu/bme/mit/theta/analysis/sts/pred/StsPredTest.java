package hu.bme.mit.theta.analysis.sts.pred;

import static hu.bme.mit.theta.analysis.algorithm.ArgUtils.isWellLabeled;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.GlobalPredItpRefinerOp;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefutationBasedRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.analysis.sts.StsExprSeqConcretizer;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.common.waitlist.FifoWaitlist;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl.Builder;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

public class StsPredTest {

	@Test
	public void test() {

		final VarDecl<IntType> vx = Var("x", Int());
		final Expr<IntType> x = vx.getRef();

		final int mod = 10;

		final Builder builder = new StsImpl.Builder();

		builder.addInit(Eq(x, Int(0)));
		builder.addTrans(And(Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))),
				Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
		builder.setProp(Not(Eq(x, Int(mod))));

		final STS sts = builder.build();

		final ItpSolver solver = Z3SolverFactory.getInstace().createItpSolver();

		final StsPredAnalysis analysis = new StsPredAnalysis(sts, solver);
		final Predicate<ExprState> target = new ExprStatePredicate(Not(sts.getProp()), solver);

		final SimplePredPrecision precision = SimplePredPrecision.create(Collections.singleton(Lt(x, Int(mod))),
				solver);

		final Abstractor<PredState, StsAction, SimplePredPrecision> abstractor = WaitlistBasedAbstractor
				.create(analysis, target, FifoWaitlist.supplier());

		final StsExprSeqConcretizer concretizerOp = new StsExprSeqConcretizer(sts, solver);
		final GlobalPredItpRefinerOp<StsAction> refinerOp = new GlobalPredItpRefinerOp<>();

		final RefutationBasedRefiner<PredState, StsAction, SimplePredPrecision, ItpRefutation> refiner = new RefutationBasedRefiner<>(
				concretizerOp, refinerOp);

		final SafetyChecker<PredState, StsAction, SimplePredPrecision> checker = CegarChecker.create(abstractor,
				refiner);

		final SafetyStatus<PredState, StsAction> safetyStatus = checker.check(precision);

		final ARG<PredState, StsAction> arg = safetyStatus.getArg();
		assertTrue(isWellLabeled(arg, solver));

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}

}
