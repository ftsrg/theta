package hu.bme.mit.theta.frontend.benchmark;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.ExplItpTraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.ExplVarSetsTraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.SimplePredItpTraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.WaitlistBasedAbstractor;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.CfaLts;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprTraceCraigItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.loc.ConstLocPrecision;
import hu.bme.mit.theta.analysis.loc.LocAction;
import hu.bme.mit.theta.analysis.loc.LocAnalysis;
import hu.bme.mit.theta.analysis.loc.LocPrecision;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.loc.LocTraceRefiner;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;

public class CfaConfigurationBuilder extends ConfigurationBuilder {

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

	public Configuration<? extends State, ? extends Action, ? extends Precision> build(final CFA cfa) {
		final ItpSolver solver = getSolverFactory().createItpSolver();
		final CfaLts lts = CfaLts.getInstance();

		if (getDomain() == Domain.EXPL) {
			final Analysis<LocState<ExplState, CfaLoc, CfaEdge>, LocAction<CfaLoc, CfaEdge>, LocPrecision<ExplPrecision, CfaLoc, CfaEdge>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), ExplAnalysis.create(solver, Exprs.True()));
			final ArgBuilder<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<ExplPrecision, CfaLoc, CfaEdge>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<ExplPrecision, CfaLoc, CfaEdge>> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, LocState::getLoc, PriorityWaitlist.supplier(getSearch().comparator),
							getLogger());

			Refiner<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<ExplPrecision, CfaLoc, CfaEdge>> refiner = null;

			switch (getRefinement()) {
			case CRAIG_ITP:
				refiner = SingleExprTraceRefiner.create(
						ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
						LocTraceRefiner.create(new ExplItpTraceRefiner<>()), getLogger());
				break;
			case SEQ_ITP:
				refiner = SingleExprTraceRefiner.create(
						ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
						LocTraceRefiner.create(new ExplItpTraceRefiner<>()), getLogger());
				break;
			case UNSAT_CORE:
				refiner = SingleExprTraceRefiner.create(
						ExprTraceUnsatCoreChecker.create(Exprs.True(), Exprs.True(), solver),
						LocTraceRefiner.create(new ExplVarSetsTraceRefiner<>()), getLogger());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<LocState<ExplState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<ExplPrecision, CfaLoc, CfaEdge>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			return Configuration.create(checker, ConstLocPrecision.create(ExplPrecision.create()));
		} else if (getDomain() == Domain.PRED) {
			final Analysis<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<SimplePredPrecision, CfaLoc, CfaEdge>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), PredAnalysis.create(solver, Exprs.True()));
			final ArgBuilder<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<SimplePredPrecision, CfaLoc, CfaEdge>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<SimplePredPrecision, CfaLoc, CfaEdge>> abstractor = WaitlistBasedAbstractor
					.create(argBuilder, LocState::getLoc, PriorityWaitlist.supplier(getSearch().comparator),
							getLogger());

			Refiner<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<SimplePredPrecision, CfaLoc, CfaEdge>> refiner = null;

			switch (getRefinement()) {
			case CRAIG_ITP:
				refiner = SingleExprTraceRefiner.create(
						ExprTraceCraigItpChecker.create(Exprs.True(), Exprs.True(), solver),
						LocTraceRefiner.create(new SimplePredItpTraceRefiner<>()), getLogger());
				break;
			case SEQ_ITP:
				refiner = SingleExprTraceRefiner.create(
						ExprTraceSeqItpChecker.create(Exprs.True(), Exprs.True(), solver),
						LocTraceRefiner.create(new SimplePredItpTraceRefiner<>()), getLogger());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<LocState<PredState, CfaLoc, CfaEdge>, CfaAction, LocPrecision<SimplePredPrecision, CfaLoc, CfaEdge>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			return Configuration.create(checker, ConstLocPrecision.create(SimplePredPrecision.create(solver)));

		} else {
			throw new UnsupportedOperationException();
		}
	}
}
