package hu.bme.mit.theta.frontend.benchmark;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.CfaLts;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprTraceCraigItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.loc.ConstLocPrec;
import hu.bme.mit.theta.analysis.loc.ConstLocPrecRefiner;
import hu.bme.mit.theta.analysis.loc.GenericLocPrec;
import hu.bme.mit.theta.analysis.loc.GenericLocPrecRefiner;
import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrec;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.pred.ItpRefToSimplePredPrec;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;

public class CfaConfigurationBuilder extends ConfigurationBuilder {

	public enum PrecGranularity {
		CONST, GEN
	};

	private PrecGranularity precGranularity = PrecGranularity.CONST;

	public CfaConfigurationBuilder(final Domain domain, final Refinement refinement) {
		super(domain, refinement);
	}

	public CfaConfigurationBuilder logger(final Logger logger) {
		setLogger(logger);
		return this;
	}

	public CfaConfigurationBuilder solverFactory(final SolverFactory solverFactory) {
		setSolverFactory(solverFactory);
		return this;
	}

	public CfaConfigurationBuilder search(final Search search) {
		setSearch(search);
		return this;
	}

	public CfaConfigurationBuilder predSplit(final PredSplit predSplit) {
		setPredSplit(predSplit);
		return this;
	}

	public CfaConfigurationBuilder precGranularity(final PrecGranularity precGranularity) {
		this.precGranularity = precGranularity;
		return this;
	}

	public Configuration<? extends State, ? extends Action, ? extends Prec> build(final CFA cfa) {
		final ItpSolver solver = getSolverFactory().createItpSolver();
		final CfaLts lts = CfaLts.getInstance();

		if (getDomain() == Domain.EXPL) {
			final Analysis<LocState<ExplState, CfaLoc, CfaEdge>, LocAction<CfaLoc, CfaEdge>, LocPrec<ExplPrec, CfaLoc, CfaEdge>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), ExplAnalysis.create(solver, Exprs.True()));
			final ArgBuilder<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrec<ExplPrec, CfaLoc, CfaEdge>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrec<ExplPrec, CfaLoc, CfaEdge>> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, LocState::getLoc, PriorityWaitlist.supplier(getSearch().comparator),
							getLogger());

			Refiner<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrec<ExplPrec, CfaLoc, CfaEdge>> refiner = null;

			switch (getRefinement()) {
			case FW_CRAIG_ITP:
				if (precGranularity == PrecGranularity.CONST) {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
							ConstLocPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				} else {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
							GenericLocPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				}
				break;
			case SEQ_ITP:
				if (precGranularity == PrecGranularity.CONST) {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
							ConstLocPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				} else {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
							GenericLocPrecRefiner.create(new ItpRefToExplPrec()), getLogger());
				}
				break;
			case UNSAT_CORE:
				if (precGranularity == PrecGranularity.CONST) {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceUnsatCoreChecker.create(Exprs.True(), Exprs.True(), solver),
							ConstLocPrecRefiner.create(new VarsRefToExplPrec()), getLogger());
				} else {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceUnsatCoreChecker.create(Exprs.True(), Exprs.True(), solver),
							GenericLocPrecRefiner.create(new VarsRefToExplPrec()), getLogger());
				}
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrec<ExplPrec, CfaLoc, CfaEdge>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			LocPrec<ExplPrec, CfaLoc, CfaEdge> prec = null;
			switch (precGranularity) {
			case CONST:
				prec = ConstLocPrec.create(ExplPrec.create());
				break;
			case GEN:
				prec = GenericLocPrec.create(ExplPrec.create());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			return Configuration.create(checker, prec);

		} else if (getDomain() == Domain.PRED) {
			final Analysis<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrec<SimplePredPrec, CfaLoc, CfaEdge>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), PredAnalysis.create(solver, Exprs.True()));
			final ArgBuilder<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrec<SimplePredPrec, CfaLoc, CfaEdge>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrec<SimplePredPrec, CfaLoc, CfaEdge>> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, LocState::getLoc, PriorityWaitlist.supplier(getSearch().comparator),
							getLogger());

			Refiner<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrec<SimplePredPrec, CfaLoc, CfaEdge>> refiner = null;

			switch (getRefinement()) {
			case FW_CRAIG_ITP:
				if (precGranularity == PrecGranularity.CONST) {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
							ConstLocPrecRefiner.create(new ItpRefToSimplePredPrec(solver, getPredSplit().splitter)),
							getLogger());
					break;
				} else {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
							GenericLocPrecRefiner.create(new ItpRefToSimplePredPrec(solver, getPredSplit().splitter)),
							getLogger());
				}
			case SEQ_ITP:
				if (precGranularity == PrecGranularity.CONST) {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
							ConstLocPrecRefiner.create(new ItpRefToSimplePredPrec(solver, getPredSplit().splitter)),
							getLogger());
				} else {
					refiner = SingleExprTraceRefiner.create(
							ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
							GenericLocPrecRefiner.create(new ItpRefToSimplePredPrec(solver, getPredSplit().splitter)),
							getLogger());
				}
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrec<SimplePredPrec, CfaLoc, CfaEdge>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			LocPrec<SimplePredPrec, CfaLoc, CfaEdge> prec = null;

			switch (precGranularity) {
			case CONST:
				prec = ConstLocPrec.create(SimplePredPrec.create(solver));
				break;
			case GEN:
				prec = GenericLocPrec.create(SimplePredPrec.create(solver));
				break;
			default:
				throw new UnsupportedOperationException();
			}

			return Configuration.create(checker, prec);

		} else {
			throw new UnsupportedOperationException();
		}
	}
}
