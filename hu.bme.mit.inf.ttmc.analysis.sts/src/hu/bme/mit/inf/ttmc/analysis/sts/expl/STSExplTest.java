package hu.bme.mit.inf.ttmc.analysis.sts.expl;

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
import java.util.function.Predicate;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ArgPrinter;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.AbstractorImpl;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.CEGARLoopImpl;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.RefutationBasedRefiner;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.refinerops.GlobalExplItpRefinerOp;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.impl.ExprStatePredicate;
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.analysis.sts.STSAction;
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

public class STSExplTest {

	@Test
	public void test() {

		final VarDecl<IntType> vx = Var("x", Int());
		final Expr<IntType> x = vx.getRef();
		final VarDecl<IntType> vy = Var("y", Int());
		final Expr<IntType> y = vy.getRef();

		final int mod = 10;

		final Builder builder = new STSImpl.Builder();

		builder.addInit(Eq(x, Int(0)));
		builder.addInit(Eq(y, Int(0)));
		builder.addTrans(And(Imply(Lt(x, Int(mod)), Eq(Prime(x), Add(x, Int(1)))),
				Imply(Geq(x, Int(mod)), Eq(Prime(x), Int(0)))));
		builder.addTrans(Eq(Prime(y), Int(0)));
		builder.setProp(Not(Eq(x, Int(mod))));

		final STS sts = builder.build();

		final SolverManager manager = new Z3SolverManager();
		final ItpSolver solver = manager.createItpSolver();

		final STSExplAnalysis analysis = new STSExplAnalysis(sts, solver);
		final Predicate<ExprState> target = new ExprStatePredicate(Not(sts.getProp()), solver);

		final GlobalExplPrecision precision = GlobalExplPrecision.create(Collections.singleton(vy));

		final Abstractor<ExplState, STSAction, ExplPrecision> abstractor = new AbstractorImpl<>(analysis, target);

		final STSExprSeqConcretizer concretizerOp = new STSExprSeqConcretizer(sts, solver);
		final GlobalExplItpRefinerOp<STSAction> refinerOp = new GlobalExplItpRefinerOp<>();

		final RefutationBasedRefiner<ExplState, ExplState, ItpRefutation, GlobalExplPrecision, STSAction> refiner = new RefutationBasedRefiner<>(
				concretizerOp, refinerOp);

		final CEGARLoopImpl<ExplState, STSAction, GlobalExplPrecision, ExplState> cegarLoop = new CEGARLoopImpl<>(
				abstractor, refiner);

		cegarLoop.check(precision);
		System.out.println(ArgPrinter.toGraphvizString(abstractor.getARG()));
		System.out.println(cegarLoop.getStatus());
	}

}
