package hu.bme.mit.theta.tools.cfa;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.cfa.CfaAction;
import hu.bme.mit.theta.analysis.cfa.CfaLts;
import hu.bme.mit.theta.analysis.cfa.ConstLocPrec;
import hu.bme.mit.theta.analysis.cfa.ConstLocPrecRefiner;
import hu.bme.mit.theta.analysis.cfa.GenericLocPrec;
import hu.bme.mit.theta.analysis.cfa.GenericLocPrecRefiner;
import hu.bme.mit.theta.analysis.cfa.LocAnalysis;
import hu.bme.mit.theta.analysis.cfa.LocPrec;
import hu.bme.mit.theta.analysis.cfa.LocState;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.pred.ItpRefToSimplePredPrec;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.tools.Configuration;
import hu.bme.mit.theta.tools.ConfigurationBuilder;

public class CfaConfigurationBuilder extends ConfigurationBuilder {

	public enum PrecGranularity {
		CONST {
			@Override
			public <P extends Prec> LocPrec<P> createPrec(final P innerPrec) {
				return ConstLocPrec.create(innerPrec);
			}

			@Override
			public <S extends State, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<LocState<S>, A, LocPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return ConstLocPrecRefiner.create(refToPrec);
			}
		},

		GEN {
			@Override
			public <P extends Prec> LocPrec<P> createPrec(final P innerPrec) {
				return GenericLocPrec.create(innerPrec);
			}

			@Override
			public <S extends State, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<LocState<S>, A, LocPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return GenericLocPrecRefiner.create(refToPrec);
			}
		};

		public abstract <P extends Prec> LocPrec<P> createPrec(P innerPrec);

		public abstract <S extends State, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<LocState<S>, A, LocPrec<P>, R> createRefiner(
				RefutationToPrec<P, R> refToPrec);
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
		final CfaLts lts = new CfaLts();

		if (getDomain() == Domain.EXPL) {
			final Analysis<LocState<ExplState>, CfaAction, LocPrec<ExplPrec>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), ExplAnalysis.create(solver, True()));
			final ArgBuilder<LocState<ExplState>, CfaAction, LocPrec<ExplPrec>> argBuilder = ArgBuilder.create(lts,
					analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<ExplState>, CfaAction, LocPrec<ExplPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(LocState::getLoc)
					.waitlistSupplier(PriorityWaitlist.supplier(getSearch().comparator)).logger(getLogger()).build();

			Refiner<LocState<ExplState>, CfaAction, LocPrec<ExplPrec>> refiner = null;

			switch (getRefinement()) {
			case FW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), getLogger());
				break;
			case BW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), getLogger());
				break;
			case SEQ_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), getLogger());
				break;
			case UNSAT_CORE:
				refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new VarsRefToExplPrec()), getLogger());
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<LocState<ExplState>, CfaAction, LocPrec<ExplPrec>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			final LocPrec<ExplPrec> prec = precGranularity.createPrec(ExplPrec.create());

			return Configuration.create(checker, prec);

		} else if (getDomain() == Domain.PRED) {
			final Analysis<LocState<PredState>, CfaAction, LocPrec<SimplePredPrec>> analysis = LocAnalysis
					.create(cfa.getInitLoc(), PredAnalysis.create(solver, True()));
			final ArgBuilder<LocState<PredState>, CfaAction, LocPrec<SimplePredPrec>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<LocState<PredState>, CfaAction, LocPrec<SimplePredPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(LocState::getLoc)
					.waitlistSupplier(PriorityWaitlist.supplier(getSearch().comparator)).logger(getLogger()).build();

			ExprTraceChecker<ItpRefutation> exprTraceChecker = null;
			switch (getRefinement()) {
			case FW_BIN_ITP:
				exprTraceChecker = ExprTraceFwBinItpChecker.create(True(), True(), solver);
				break;
			case BW_BIN_ITP:
				exprTraceChecker = ExprTraceBwBinItpChecker.create(True(), True(), solver);
				break;
			case SEQ_ITP:
				exprTraceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);
				break;
			default:
				throw new UnsupportedOperationException();
			}
			final ItpRefToSimplePredPrec refToPrec = new ItpRefToSimplePredPrec(solver, getPredSplit().splitter);
			final Refiner<LocState<PredState>, CfaAction, LocPrec<SimplePredPrec>> refiner = SingleExprTraceRefiner
					.create(exprTraceChecker, precGranularity.createRefiner(refToPrec), getLogger());

			final SafetyChecker<LocState<PredState>, CfaAction, LocPrec<SimplePredPrec>> checker = CegarChecker
					.create(abstractor, refiner, getLogger());

			final LocPrec<SimplePredPrec> prec = precGranularity.createPrec(SimplePredPrec.create(solver));

			return Configuration.create(checker, prec);

		} else {
			throw new UnsupportedOperationException();
		}
	}
}
