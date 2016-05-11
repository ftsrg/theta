package hu.bme.mit.inf.ttmc.analysis.tests;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Ite;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Prime;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.BasicAlgorithm;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplDomain;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.analysis.expl.STSExplAbstraction;
import hu.bme.mit.inf.ttmc.analysis.expl.precisions.GlobalExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredDomain;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.analysis.pred.STSPredAbstraction;
import hu.bme.mit.inf.ttmc.analysis.pred.precisions.GlobalPredPrecision;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl.Builder;
import hu.bme.mit.inf.ttmc.solver.Solver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class STSTests {

	SolverManager manager;
	Solver solver;
	STS sts;

	@Before
	public void setup() {
		manager = new Z3SolverManager();
		solver = manager.createSolver(true, false);
		sts = createSimpleSTS();
		System.out.println(sts);
	}

	@Test
	public void testPred() {
		final Collection<Expr<? extends BoolType>> preds = new ArrayList<>();
		preds.addAll(((OrExpr) sts.getProp()).getOps());
		final STSPredAbstraction stsAbstraction = new STSPredAbstraction(sts, solver);
		final BasicAlgorithm<PredState, PredPrecision> algorithm = new BasicAlgorithm<>(PredDomain.create(solver, sts), stsAbstraction);

		final Collection<PredState> result = algorithm.run(GlobalPredPrecision.create(preds));

		System.out.println("Error reached: " + algorithm.isErrorReached());
		for (final PredState predState : result) {
			System.out.println(predState);
		}
	}

	@Test
	public void testExpl() {
		final Set<VarDecl<? extends Type>> visibleVars = sts.getVars().stream().filter(v -> v.getName().equals("x") || v.getName().equals("y"))
				.collect(Collectors.toSet());
		final Set<VarDecl<? extends Type>> invisibleVars = sts.getVars().stream().filter(v -> !visibleVars.contains(v)).collect(Collectors.toSet());

		final STSExplAbstraction stsAbstraction = new STSExplAbstraction(sts, solver);
		final BasicAlgorithm<ExplState, ExplPrecision> algorithm = new BasicAlgorithm<>(ExplDomain.create(), stsAbstraction);

		final Collection<ExplState> result = algorithm.run(GlobalExplPrecision.create(visibleVars, invisibleVars));

		System.out.println("Error reached: " + algorithm.isErrorReached());
		for (final ExplState predState : result) {
			System.out.println(predState);
		}
	}

	private static STS createSimpleSTS() {
		final Builder builder = new STSImpl.Builder();
		final VarDecl<IntType> r = Decls2.Var("r", Types.Int());
		final VarDecl<IntType> x = Decls2.Var("x", Types.Int());
		final VarDecl<IntType> y = Decls2.Var("y", Types.Int());

		builder.addInvar(Leq(Int(0), r.getRef()));
		builder.addInvar(Leq(Int(0), x.getRef()));
		builder.addInvar(Leq(Int(0), y.getRef()));
		builder.addInvar(Leq(r.getRef(), Int(1)));
		builder.addInvar(Leq(x.getRef(), Int(2)));
		builder.addInvar(Leq(y.getRef(), Int(2)));

		builder.addInit(Eq(r.getRef(), Int(0)));
		builder.addInit(Eq(x.getRef(), Int(0)));
		builder.addInit(Eq(y.getRef(), Int(1)));

		builder.addTrans(And(Geq(Prime(r.getRef()), Int(0)), Leq(Prime(r.getRef()), Int(1))));
		builder.addTrans(Eq(Prime(x.getRef()), Ite(Eq(r.getRef(), Int(1)), Int(0),
				Ite(Lt(x.getRef(), y.getRef()), Add(x.getRef(), Int(1)), Ite(Eq(x.getRef(), y.getRef()), Int(0), x.getRef())))));
		builder.addTrans(Eq(Prime(y.getRef()), Ite(Eq(r.getRef(), Int(1)), Int(0), Ite(And(Eq(x.getRef(), y.getRef()), Not(Eq(y.getRef(), Int(2)))),
				Add(y.getRef(), Int(1)), Ite(Eq(x.getRef(), y.getRef()), Int(0), y.getRef())))));

		builder.setProp(Or(Lt(x.getRef(), y.getRef()), Eq(r.getRef(), Int(1))));

		return builder.build();
	}
}
