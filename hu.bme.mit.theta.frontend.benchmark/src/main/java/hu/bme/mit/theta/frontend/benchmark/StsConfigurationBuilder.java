package hu.bme.mit.theta.frontend.benchmark;

import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.pred.ItpRefToSimplePredPrec;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.sts.StsAction;
import hu.bme.mit.theta.analysis.sts.StsEmptyInitPrec;
import hu.bme.mit.theta.analysis.sts.StsInitPrec;
import hu.bme.mit.theta.analysis.sts.StsLts;
import hu.bme.mit.theta.analysis.sts.StsPropInitPrec;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;

public final class StsConfigurationBuilder extends ConfigurationBuilder {

	public enum InitPrec {
		EMPTY, PROP
	};

	private InitPrec initPrec = InitPrec.EMPTY;

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

	public StsConfigurationBuilder predSplit(final PredSplit predSplit) {
		setPredSplit(predSplit);
		return this;
	}

	public StsConfigurationBuilder initPrec(final InitPrec initPrec) {
		this.initPrec = initPrec;
		return this;
	}

	public InitPrec getInitPrec() {
		return initPrec;
	}

	public Configuration<? extends State, ? extends Action, ? extends Prec> build(final STS sts) {
		final ItpSolver solver = getSolverFactory().createItpSolver();
		final LTS<State, StsAction> lts = StsLts.create(sts);
		final Expr<? extends BoolType> init = And(sts.getInit());
		final Expr<? extends BoolType> negProp = Not(sts.getProp());

		StsInitPrec initPrecBuilder = null;
		switch (initPrec) {
		case EMPTY:
			initPrecBuilder = new StsEmptyInitPrec();
			break;
		case PROP:
			initPrecBuilder = new StsPropInitPrec();
			break;
		default:
			throw new UnsupportedOperationException();
		}

		if (getDomain() == Domain.EXPL) {
			final Predicate<ExplState> target = new ExplStatePredicate(negProp, solver);
			final Analysis<ExplState, ExprAction, ExplPrec> analysis = ExplAnalysis.create(solver, init);
			final ArgBuilder<ExplState, StsAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis, target);
			final Abstractor<ExplState, StsAction, ExplPrec> abstractor = WaitlistBasedAbstractor.create(argBuilder,
					PriorityWaitlist.supplier(getSearch().comparator), getLogger());

			Refiner<ExplState, StsAction, ExplPrec> refiner = null;

			switch (getRefinement()) {
			case FW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(init, negProp, solver),
						JoiningPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				break;
			case BW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(init, negProp, solver),
						JoiningPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				break;
			case SEQ_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(init, negProp, solver),
						JoiningPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				break;
			case UNSAT_CORE:
				refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(init, negProp, solver),
						JoiningPrecRefiner.create(new VarsRefToExplPrec()), getLogger());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<ExplState, StsAction, ExplPrec> checker = CegarChecker.create(abstractor, refiner,
					getLogger());
			final ExplPrec prec = initPrecBuilder.createExpl(sts);
			return Configuration.create(checker, prec);

		} else if (getDomain() == Domain.PRED) {
			final Predicate<ExprState> target = new ExprStatePredicate(negProp, solver);
			final Analysis<PredState, ExprAction, PredPrec> analysis = PredAnalysis.create(solver, init);
			final ArgBuilder<PredState, StsAction, SimplePredPrec> argBuilder = ArgBuilder.create(lts, analysis,
					target);
			final Abstractor<PredState, StsAction, SimplePredPrec> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, PriorityWaitlist.supplier(getSearch().comparator), getLogger());

			ExprTraceChecker<ItpRefutation> exprTraceChecker = null;
			switch (getRefinement()) {
			case FW_BIN_ITP:
				exprTraceChecker = ExprTraceFwBinItpChecker.create(init, negProp, solver);
				break;
			case BW_BIN_ITP:
				exprTraceChecker = ExprTraceBwBinItpChecker.create(init, negProp, solver);
				break;
			case SEQ_ITP:
				exprTraceChecker = ExprTraceSeqItpChecker.create(init, negProp, solver);
				break;
			default:
				throw new UnsupportedOperationException();
			}
			final Refiner<PredState, StsAction, SimplePredPrec> refiner = SingleExprTraceRefiner.create(
					exprTraceChecker,
					JoiningPrecRefiner.create(new ItpRefToSimplePredPrec(solver, getPredSplit().splitter)),
					getLogger());

			final SafetyChecker<PredState, StsAction, SimplePredPrec> checker = CegarChecker.create(abstractor, refiner,
					getLogger());

			final SimplePredPrec prec = initPrecBuilder.createSimplePred(sts, solver);
			return Configuration.create(checker, prec);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
