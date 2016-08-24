package hu.bme.mit.inf.theta.analysis.sts.pred;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2.Prime;

import java.util.Collections;
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.inf.theta.analysis.ExprState;
import hu.bme.mit.inf.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.theta.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.ARGNode;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.CEGARLoopImpl;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.RefutationBasedRefiner;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.WaitlistBasedAbstractorImpl;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.refinerops.GlobalPredItpRefinerOp;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.waitlist.Waitlist;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.waitlist.impl.LIFOWaitlist;
import hu.bme.mit.inf.theta.analysis.expl.ExplState;
import hu.bme.mit.inf.theta.analysis.impl.ExprStatePredicate;
import hu.bme.mit.inf.theta.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredPrecision;
import hu.bme.mit.inf.theta.analysis.pred.PredState;
import hu.bme.mit.inf.theta.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.theta.analysis.sts.StsAction;
import hu.bme.mit.inf.theta.analysis.sts.StsExprSeqConcretizer;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl.Builder;
import hu.bme.mit.inf.theta.solver.ItpSolver;
import hu.bme.mit.inf.theta.solver.SolverManager;
import hu.bme.mit.inf.theta.solver.z3.Z3SolverManager;

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

		final GlobalPredPrecision precision = GlobalPredPrecision.create(Collections.singleton(Lt(x, Int(mod))));

		final Waitlist<ARGNode<PredState, StsAction>> waitlist = new LIFOWaitlist<>();

		final Abstractor<PredState, StsAction, PredPrecision> abstractor = new WaitlistBasedAbstractorImpl<>(analysis,
				target, waitlist);

		final StsExprSeqConcretizer concretizerOp = new StsExprSeqConcretizer(sts, solver);
		final GlobalPredItpRefinerOp<StsAction> refinerOp = new GlobalPredItpRefinerOp<>();

		final RefutationBasedRefiner<PredState, ExplState, ItpRefutation, GlobalPredPrecision, StsAction> refiner = new RefutationBasedRefiner<>(
				concretizerOp, refinerOp);

		final CEGARLoopImpl<PredState, StsAction, GlobalPredPrecision, ExplState> cegarLoop = new CEGARLoopImpl<>(
				abstractor, refiner);

		cegarLoop.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
		System.out.println(cegarLoop.getStatus());

	}

}
