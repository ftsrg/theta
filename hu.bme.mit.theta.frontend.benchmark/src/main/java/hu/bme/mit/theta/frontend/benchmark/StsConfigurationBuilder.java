package hu.bme.mit.theta.frontend.benchmark;

import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.ExplItpRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.ExplVarSetsRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.SimplePredItpRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceCraigItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.analysis.sts.StsLts;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;

public final class StsConfigurationBuilder extends ConfigurationBuilder {

	public enum InitPrecision {
		EMPTY, PROP
	};

	private InitPrecision initPrecision = InitPrecision.EMPTY;

	public StsConfigurationBuilder(final Domain domain, final Refinement refinement) {
		super(domain, refinement);
	}

	public StsConfigurationBuilder logger(final Logger logger) {
		setLogger(logger);
		return this;
	}

	public StsConfigurationBuilder solverFactory(final SolverFactory solverFactory) {
		setSolverFactory(solverFactory);
		return this;
	}

	public StsConfigurationBuilder search(final Search search) {
		setSearch(search);
		return this;
	}

	public StsConfigurationBuilder initPrecision(final InitPrecision initPrecision) {
		this.initPrecision = initPrecision;
		return this;
	}

	public InitPrecision getInitPrecision() {
		return initPrecision;
	}

	public Configuration<? extends State, ? extends Action, ? extends Precision> build(final STS sts) {
		final ItpSolver solver = getSolverFactory().createItpSolver();
		final LTS<State, StsAction> lts = StsLts.create(sts);
		final Expr<? extends BoolType> init = And(sts.getInit());
		final Expr<? extends BoolType> negProp = Not(sts.getProp());
		final Predicate<ExprState> target = new ExprStatePredicate(negProp, solver);

		if (getDomain() == Domain.EXPL) {

			final Analysis<ExplState, ExprAction, ExplPrecision> analysis = ExplAnalysis.create(solver, init);
			final ArgBuilder<ExplState, StsAction, ExplPrecision> argBuilder = ArgBuilder.create(lts, analysis, target);
			final Abstractor<ExplState, StsAction, ExplPrecision> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, PriorityWaitlist.supplier(getSearch().comparator), getLogger());

			Refiner<ExplState, StsAction, ExplPrecision> refiner = null;

			switch (getRefinement()) {
			case CRAIG_ITP:
				refiner = ExplItpRefiner.create(ExprTraceCraigItpChecker.create(init, negProp, solver), getLogger());
				break;
			case SEQ_ITP:
				refiner = ExplItpRefiner.create(ExprTraceSeqItpChecker.create(init, negProp, solver), getLogger());
				break;
			case UNSAT_CORE:
				refiner = ExplVarSetsRefiner.create(ExprTraceUnsatCoreChecker.create(init, negProp, solver),
						getLogger());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<ExplState, StsAction, ExplPrecision> checker = CegarChecker.create(abstractor, refiner,
					getLogger());
			ExplPrecision precision = null;
			switch (initPrecision) {
			case EMPTY:
				precision = ExplPrecision.create();
				break;
			case PROP:
				precision = ExplPrecision.create(ExprUtils.getVars(negProp));
				break;
			default:
				throw new UnsupportedOperationException();
			}

			return Configuration.create(checker, precision);

		} else if (getDomain() == Domain.PRED) {
			final Analysis<PredState, ExprAction, PredPrecision> analysis = PredAnalysis.create(solver, init);
			final ArgBuilder<PredState, StsAction, SimplePredPrecision> argBuilder = ArgBuilder.create(lts, analysis,
					target);
			final Abstractor<PredState, StsAction, SimplePredPrecision> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, PriorityWaitlist.supplier(getSearch().comparator), getLogger());

			ExprTraceChecker<ItpRefutation> exprTraceChecker = null;
			switch (getRefinement()) {
			case CRAIG_ITP:
				exprTraceChecker = ExprTraceCraigItpChecker.create(init, negProp, solver);
				break;
			case SEQ_ITP:
				exprTraceChecker = ExprTraceSeqItpChecker.create(init, negProp, solver);
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final Refiner<PredState, StsAction, SimplePredPrecision> refiner = SimplePredItpRefiner
					.create(exprTraceChecker, getLogger());

			final SafetyChecker<PredState, StsAction, SimplePredPrecision> checker = CegarChecker.create(abstractor,
					refiner, getLogger());
			SimplePredPrecision precision = null;
			switch (initPrecision) {
			case EMPTY:
				precision = SimplePredPrecision.create(solver);
				break;
			case PROP:
				precision = SimplePredPrecision.create(ExprUtils.getAtoms(negProp), solver);
				break;
			default:
				throw new UnsupportedOperationException();
			}

			return Configuration.create(checker, precision);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
