package hu.bme.mit.theta.tools.cfa;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprState;
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
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.ItpRefToSimplePredPrec;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrec;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAction;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaAnalysis;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaLts;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.GlobalCfaPrecRefiner;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.LocalCfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.prec.LocalCfaPrecRefiner;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.tools.Config;

public class CfaConfigBuilder {
	public enum Domain {
		EXPL, PRED
	};

	public enum Refinement {
		FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, UNSAT_CORE
	};

	public enum Search {
		BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),

		DFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

		public final ArgNodeComparator comparator;

		private Search(final ArgNodeComparator comparator) {
			this.comparator = comparator;
		}

	};

	public enum PredSplit {
		WHOLE(ExprSplitters.whole()),

		CONJUNCTS(ExprSplitters.conjuncts()),

		ATOMS(ExprSplitters.atoms());

		public final ExprSplitter splitter;

		private PredSplit(final ExprSplitter splitter) {
			this.splitter = splitter;
		}
	};

	public enum PrecGranularity {
		GLOBAL {
			@Override
			public <P extends Prec> CfaPrec<P> createPrec(final P innerPrec) {
				return GlobalCfaPrec.create(innerPrec);
			}

			@Override
			public <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return GlobalCfaPrecRefiner.create(refToPrec);
			}
		},

		LOCAL {
			@Override
			public <P extends Prec> CfaPrec<P> createPrec(final P innerPrec) {
				return LocalCfaPrec.create(innerPrec);
			}

			@Override
			public <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return LocalCfaPrecRefiner.create(refToPrec);
			}
		};

		public abstract <P extends Prec> CfaPrec<P> createPrec(P innerPrec);

		public abstract <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> createRefiner(
				RefutationToPrec<P, R> refToPrec);
	};

	private Logger logger = NullLogger.getInstance();
	private SolverFactory solverFactory = Z3SolverFactory.getInstace();
	private final Domain domain;
	private final Refinement refinement;
	private Search search = Search.BFS;
	private PredSplit predSplit = PredSplit.WHOLE;
	private PrecGranularity precGranularity = PrecGranularity.GLOBAL;

	public CfaConfigBuilder(final Domain domain, final Refinement refinement) {
		this.domain = domain;
		this.refinement = refinement;
	}

	public CfaConfigBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public CfaConfigBuilder solverFactory(final SolverFactory solverFactory) {
		this.solverFactory = solverFactory;
		return this;
	}

	public CfaConfigBuilder search(final Search search) {
		this.search = search;
		return this;
	}

	public CfaConfigBuilder predSplit(final PredSplit predSplit) {
		this.predSplit = predSplit;
		return this;
	}

	public CfaConfigBuilder precGranularity(final PrecGranularity precGranularity) {
		this.precGranularity = precGranularity;
		return this;
	}

	public Config<? extends State, ? extends Action, ? extends Prec> build(final CFA cfa) {
		final ItpSolver solver = solverFactory.createItpSolver();
		final CfaLts lts = new CfaLts();

		if (domain == Domain.EXPL) {
			final Analysis<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> analysis = CfaAnalysis
					.create(cfa.getInitLoc(), ExplAnalysis.create(solver, True()));
			final ArgBuilder<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> argBuilder = ArgBuilder.create(lts,
					analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(CfaState::getLoc)
					.waitlistSupplier(PriorityWaitlist.supplier(search.comparator)).logger(logger).build();

			Refiner<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> refiner = null;

			switch (refinement) {
			case FW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), logger);
				break;
			case BW_BIN_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), logger);
				break;
			case SEQ_ITP:
				refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new ItpRefToExplPrec()), logger);
				break;
			case UNSAT_CORE:
				refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(True(), True(), solver),
						precGranularity.createRefiner(new VarsRefToExplPrec()), logger);
				break;
			default:
				throw new UnsupportedOperationException();
			}

			final SafetyChecker<CfaState<ExplState>, CfaAction, CfaPrec<ExplPrec>> checker = CegarChecker
					.create(abstractor, refiner, logger);

			final CfaPrec<ExplPrec> prec = precGranularity.createPrec(ExplPrec.create());

			return Config.create(checker, prec);

		} else if (domain == Domain.PRED) {
			final Analysis<CfaState<PredState>, CfaAction, CfaPrec<SimplePredPrec>> analysis = CfaAnalysis
					.create(cfa.getInitLoc(), PredAnalysis.create(solver, True()));
			final ArgBuilder<CfaState<PredState>, CfaAction, CfaPrec<SimplePredPrec>> argBuilder = ArgBuilder
					.create(lts, analysis, s -> s.getLoc().equals(cfa.getErrorLoc()));
			final Abstractor<CfaState<PredState>, CfaAction, CfaPrec<SimplePredPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(CfaState::getLoc)
					.waitlistSupplier(PriorityWaitlist.supplier(search.comparator)).logger(logger).build();

			ExprTraceChecker<ItpRefutation> exprTraceChecker = null;
			switch (refinement) {
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
			final ItpRefToSimplePredPrec refToPrec = new ItpRefToSimplePredPrec(solver, predSplit.splitter);
			final Refiner<CfaState<PredState>, CfaAction, CfaPrec<SimplePredPrec>> refiner = SingleExprTraceRefiner
					.create(exprTraceChecker, precGranularity.createRefiner(refToPrec), logger);

			final SafetyChecker<CfaState<PredState>, CfaAction, CfaPrec<SimplePredPrec>> checker = CegarChecker
					.create(abstractor, refiner, logger);

			final CfaPrec<SimplePredPrec> prec = precGranularity.createPrec(SimplePredPrec.create(solver));

			return Config.create(checker, prec);

		} else {
			throw new UnsupportedOperationException();
		}
	}
}
