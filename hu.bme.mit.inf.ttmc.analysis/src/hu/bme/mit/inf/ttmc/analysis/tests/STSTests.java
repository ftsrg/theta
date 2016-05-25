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

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CEGARLoop;
import hu.bme.mit.inf.ttmc.analysis.algorithm.checker.Checker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.checker.impl.BasicChecker;
import hu.bme.mit.inf.ttmc.analysis.algorithm.concretizer.Concretizer;
import hu.bme.mit.inf.ttmc.analysis.algorithm.concretizer.impl.STSExprSeqConcretizer;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.BasicAlgorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.CEGARLoopImpl;
import hu.bme.mit.inf.ttmc.analysis.algorithm.refiner.Refiner;
import hu.bme.mit.inf.ttmc.analysis.algorithm.refiner.impl.PredGlobalItpRefiner;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGDomain;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGFormalismAbstraction;
import hu.bme.mit.inf.ttmc.analysis.arg.ARGState;
import hu.bme.mit.inf.ttmc.analysis.arg.utils.ArgPrinter;
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
import hu.bme.mit.inf.ttmc.analysis.refutation.ItpRefutation;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl.Builder;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.solver.SolverManager;
import hu.bme.mit.inf.ttmc.solver.z3.Z3SolverManager;

public class STSTests {

	SolverManager manager;
	ItpSolver solver;
	STS sts;

	@Before
	public void setup() {
		manager = new Z3SolverManager();
		solver = manager.createItpSolver();
		sts = createSimpleSTS();
		System.out.println(sts);
	}

	@Test
	public void testCegar() {
		final Collection<Expr<? extends BoolType>> preds = new ArrayList<>();
		preds.add(Exprs.True());
		final STSPredAbstraction stsAbstraction = STSPredAbstraction.create(sts, solver);
		final PredDomain domain = PredDomain.create(solver, sts);
		final GlobalPredPrecision precision = GlobalPredPrecision.create(preds);

		final Checker<STS, PredState, PredPrecision> checker = BasicChecker.create(domain, stsAbstraction);

		final Concretizer<STS, ExprState, ItpRefutation> concretizer = STSExprSeqConcretizer.create(sts, solver);

		final Refiner<PredState, GlobalPredPrecision, ItpRefutation> refiner = PredGlobalItpRefiner.create();

		final CEGARLoop<GlobalPredPrecision> cegarLoop = CEGARLoopImpl.create(checker, concretizer, refiner);

		System.out.println(cegarLoop.check(precision));

	}

	//@Test
	public void testPred() {
		final Collection<Expr<? extends BoolType>> preds = new ArrayList<>();
		preds.addAll(((OrExpr) sts.getProp()).getOps());
		final STSPredAbstraction stsAbstraction = STSPredAbstraction.create(sts, solver);
		final BasicAlgorithm<STS, PredState, PredPrecision> algorithm = new BasicAlgorithm<>(PredDomain.create(solver, sts), stsAbstraction);

		final Collection<PredState> result = algorithm.run(GlobalPredPrecision.create(preds));

		for (final PredState state : result) {
			System.out.println(state);
		}
	}

	//@Test
	public void testExpl() {
		final Set<VarDecl<? extends Type>> visibleVars = sts.getVars().stream().filter(v -> v.getName().equals("x") || v.getName().equals("y"))
				.collect(Collectors.toSet());
		final Set<VarDecl<? extends Type>> invisibleVars = sts.getVars().stream().filter(v -> !visibleVars.contains(v)).collect(Collectors.toSet());

		final STSExplAbstraction stsAbstraction = STSExplAbstraction.create(sts, solver);
		final BasicAlgorithm<STS, ExplState, ExplPrecision> algorithm = new BasicAlgorithm<>(ExplDomain.create(), stsAbstraction);

		final Collection<ExplState> result = algorithm.run(GlobalExplPrecision.create(visibleVars, invisibleVars));

		for (final ExplState state : result) {
			System.out.println(state);
		}
	}

	//@Test
	public void testArgWithExpl() {
		final Set<VarDecl<? extends Type>> visibleVars = sts.getVars().stream().filter(v -> v.getName().equals("x") || v.getName().equals("y"))
				.collect(Collectors.toSet());
		final Set<VarDecl<? extends Type>> invisibleVars = sts.getVars().stream().filter(v -> !visibleVars.contains(v)).collect(Collectors.toSet());

		final ARGFormalismAbstraction<STS, ExplState, ExplPrecision> stsAbstraction = ARGFormalismAbstraction.create(STSExplAbstraction.create(sts, solver));
		final BasicAlgorithm<STS, ARGState<ExplState>, ExplPrecision> algorithm = new BasicAlgorithm<>(ARGDomain.create(ExplDomain.create()), stsAbstraction);

		final Collection<ARGState<ExplState>> result = algorithm.run(GlobalExplPrecision.create(visibleVars, invisibleVars));

		for (final ARGState<ExplState> state : result) {
			System.out.println(state);
		}

		System.out.println(ArgPrinter.toGraphvizString(result));
	}

	//@Test
	public void testArgWithPred() {
		final Collection<Expr<? extends BoolType>> preds = new ArrayList<>();
		preds.addAll(((OrExpr) sts.getProp()).getOps());
		final ARGFormalismAbstraction<STS, PredState, PredPrecision> stsAbstraction = ARGFormalismAbstraction.create(STSPredAbstraction.create(sts, solver));
		final BasicAlgorithm<STS, ARGState<PredState>, PredPrecision> algorithm = new BasicAlgorithm<>(ARGDomain.create(PredDomain.create(solver, sts)),
				stsAbstraction);

		final Collection<ARGState<PredState>> result = algorithm.run(GlobalPredPrecision.create(preds));

		for (final ARGState<PredState> state : result) {
			System.out.println(state);
		}

		System.out.println(ArgPrinter.toGraphvizString(result));
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
