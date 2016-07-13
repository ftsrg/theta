package hu.bme.mit.inf.ttmc.analysis.sts.pred;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;

import java.util.Collections;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARGNode;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.CEGARLoopImpl;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.RefutationBasedRefiner;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.WaitlistBasedAbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.refinerops.GlobalPredItpRefinerOp;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.waitlist.impl.FIFOWaitlist;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.pred.GlobalPredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredDomain;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAction;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAnalysisContext;
import hu.bme.mit.inf.ttmc.analysis.sts.STSExprSeqConcretizer;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl.Builder;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class STSPredTest {

	@Test
	public void test() {

		final VarDecl<IntType> vx = Var("x", Int());
		final Expr<IntType> x = vx.getRef();

		final int mod = 10;

		final Builder builder = new STSImpl.Builder();

		builder.addInit(Eq(x, Int(0)));
		builder.addTrans(And(Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))), Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
		builder.setProp(Not(Eq(x, Int(mod))));

		final STS sts = builder.build();

		final STSAnalysisContext context = new STSAnalysisContext(sts);

		final SolverManager manager = new Z3SolverManager();
		final ItpSolver solver = manager.createItpSolver();

		final PredDomain domain = PredDomain.create(solver);

		final STSPredInitFunction initFunction = new STSPredInitFunction(sts, solver);
		final STSPredTransferFunction transferFunction = new STSPredTransferFunction(sts, solver);
		final STSPredTargetPredicate targetPredicate = new STSPredTargetPredicate(sts, solver);

		final GlobalPredPrecision precision = GlobalPredPrecision.create(Collections.singleton(Lt(x, Int(mod))));

		final FIFOWaitlist<ARGNode<PredState, STSAction>> waitlist = new FIFOWaitlist<>();

		final Abstractor<PredState, STSAction, PredPrecision> abstractor = new WaitlistBasedAbstractorImpl<>(context, domain, initFunction, transferFunction,
				targetPredicate, waitlist);

		final STSExprSeqConcretizer concretizerOp = new STSExprSeqConcretizer(sts, solver);
		final GlobalPredItpRefinerOp<STSAction> refinerOp = new GlobalPredItpRefinerOp<>();

		final RefutationBasedRefiner<PredState, ExplState, ItpRefutation, GlobalPredPrecision, STSAction> refiner = new RefutationBasedRefiner<>(concretizerOp,
				refinerOp);

		final CEGARLoopImpl<PredState, STSAction, GlobalPredPrecision, ExplState> cegarLoop = new CEGARLoopImpl<>(abstractor, refiner);

		cegarLoop.check(precision);

		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
		System.out.println(cegarLoop.getStatus());

	}

}
