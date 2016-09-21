package hu.bme.mit.theta.analysis.sts.pred;

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

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.theta.analysis.ExprState;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.theta.analysis.algorithm.LifoWaitlist;
import hu.bme.mit.theta.analysis.algorithm.Waitlist;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarLoopImpl;
import hu.bme.mit.theta.analysis.algorithm.cegar.GlobalPredItpRefinerOp;
import hu.bme.mit.theta.analysis.algorithm.cegar.ItpRefutation;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefutationBasedRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractorImpl;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.ExprStatePredicate;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.analysis.sts.StsExprSeqConcretizer;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl.Builder;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;

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

		final SolverManager manager = new Z3SolverManager();
		final ItpSolver solver = manager.createItpSolver();

		final StsPredAnalysis analysis = new StsPredAnalysis(sts, solver);
		final Predicate<ExprState> target = new ExprStatePredicate(Not(sts.getProp()), solver);

		final SimplePredPrecision precision = SimplePredPrecision.create(Collections.singleton(Lt(x, Int(mod))));

		final Waitlist<ArgNode<PredState, StsAction>> waitlist = new LifoWaitlist<>();

		final Abstractor<PredState, StsAction, PredPrecision> abstractor = new WaitlistBasedAbstractorImpl<>(analysis,
				target, waitlist);

		final StsExprSeqConcretizer concretizerOp = new StsExprSeqConcretizer(sts, solver);
		final GlobalPredItpRefinerOp<StsAction> refinerOp = new GlobalPredItpRefinerOp<>();

		final RefutationBasedRefiner<PredState, ExplState, ItpRefutation, SimplePredPrecision, StsAction> refiner = new RefutationBasedRefiner<>(
				concretizerOp, refinerOp);

		final CegarLoopImpl<PredState, StsAction, SimplePredPrecision, ExplState> cegarLoop = new CegarLoopImpl<>(
				abstractor, refiner);

		cegarLoop.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
		System.out.println(cegarLoop.getStatus());

	}

}
