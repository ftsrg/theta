package hu.bme.mit.theta.xsts.analysis.config.combined;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.prod2.*;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.*;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.analysis.utils.ValuationExtractor;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.timed.*;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfig;
import hu.bme.mit.theta.xsts.analysis.config.XstsConfigBuilder;

import java.util.Collection;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

@SuppressWarnings({"rawtypes", "unchecked"})
public final class XstsCombinedConfigBuilder {

	public enum Search {
		BFS(SearchStrategy.BFS),

		DFS(SearchStrategy.DFS);

		public final SearchStrategy strategy;

		private Search(final SearchStrategy strategy) {
			this.strategy = strategy;
		}
	}

	public enum ZoneRefinement {
		BW_ITP, FW_ITP
	}
	
	public enum ClockStrategy {

		NONE(XstsClockReplacers.None(), false, false),

		INT(XstsClockReplacers.Int(), false, false),

		RAT(XstsClockReplacers.Rat(), false, false),
		
		CF_SPLIT_ALL(XstsClockReplacers.None(), true, false),

		CF_SPLIT_FILTERCF(XstsClockReplacers.None(), true, true);

		public final XstsClockReplacers.XstsClockReplacer clockReplacer;
		public final boolean controlFlowSplitting;
		public final boolean filterInfeasibleCF;

		private ClockStrategy(final XstsClockReplacers.XstsClockReplacer clockReplacer, final boolean controlFlowSplitting, final boolean filterInfeasibleCF) {
			this.clockReplacer = clockReplacer;
			this.controlFlowSplitting = controlFlowSplitting;
			this.filterInfeasibleCF = filterInfeasibleCF;
		}
	}

	private Logger logger = NullLogger.getInstance();
	private final SolverFactory solverFactory;
	private final XstsConfigBuilder.Domain domain;
	private final XstsConfigBuilder.Refinement refinement;
	private Search search = Search.BFS;
	private XstsConfigBuilder.PredSplit predSplit = XstsConfigBuilder.PredSplit.WHOLE;
	private int maxEnum = 0;
	private XstsConfigBuilder.InitPrec initPrec = XstsConfigBuilder.InitPrec.EMPTY;
	private PruneStrategy pruneStrategy = PruneStrategy.LAZY;
	private XstsConfigBuilder.OptimizeStmts optimizeStmts = XstsConfigBuilder.OptimizeStmts.ON;
	private XstsConfigBuilder.AutoExpl autoExpl = XstsConfigBuilder.AutoExpl.NEWOPERANDS;
	private ZoneRefinement zoneRefinement = ZoneRefinement.BW_ITP;
	private TimedXstsActionProjections timedXstsActionProjections;
	private ClockStrategy clockStrategy = ClockStrategy.NONE;

	public XstsCombinedConfigBuilder(final XstsConfigBuilder.Domain domain, final XstsConfigBuilder.Refinement refinement, final SolverFactory solverFactory) {
		this.domain = domain;
		this.refinement = refinement;
		this.solverFactory = solverFactory;
	}

	public XstsCombinedConfigBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public XstsCombinedConfigBuilder search(final Search search) {
		this.search = search;
		return this;
	}

	public XstsCombinedConfigBuilder predSplit(final XstsConfigBuilder.PredSplit predSplit) {
		this.predSplit = predSplit;
		return this;
	}

	public XstsCombinedConfigBuilder maxEnum(final int maxEnum) {
		this.maxEnum = maxEnum;
		return this;
	}

	public XstsCombinedConfigBuilder initPrec(final XstsConfigBuilder.InitPrec initPrec) {
		this.initPrec = initPrec;
		return this;
	}

	public XstsCombinedConfigBuilder pruneStrategy(final PruneStrategy pruneStrategy) {
		this.pruneStrategy = pruneStrategy;
		return this;
	}

	public XstsCombinedConfigBuilder optimizeStmts(final XstsConfigBuilder.OptimizeStmts optimizeStmts) {
		this.optimizeStmts = optimizeStmts;
		return this;
	}

	public XstsCombinedConfigBuilder autoExpl(final XstsConfigBuilder.AutoExpl autoExpl) {
		this.autoExpl = autoExpl;
		return this;
	}

	public XstsCombinedConfigBuilder zoneRefinement(final ZoneRefinement zoneRefinement) {
		this.zoneRefinement = zoneRefinement;
		return this;
	}
	
	public XstsCombinedConfigBuilder clockStrategy(final ClockStrategy clockStrategy) {
		this.clockStrategy = clockStrategy;
		return this;
	}

	public XstsConfig<? extends State, ? extends Action, ? extends Prec> build(XSTS xsts) {
		final Solver abstractionSolver = solverFactory.createSolver();

		timedXstsActionProjections = TimedXstsActionProjections.create();

		xsts = clockStrategy.clockReplacer.apply(xsts);

		final Expr<BoolType> initFormula = xsts.getInitFormula();
		final Expr<BoolType> negProp = Not(xsts.getProp());

		final Collection<VarDecl<ClockType>> clockVars = xsts.getVars().stream()
				.filter(v -> v.getType() instanceof ClockType)
				.map(v -> cast(v, Clock()))
				.toList();
		final ZonePrec zonePrec = ZonePrec.of(clockVars);
		final LazyStrategy lazyClockStrategy = createLazyZoneStrategy(zonePrec);

		final Lens lazyToConcrProd2Lens = XstsLazyLensUtils.createConcrProd2Lens();

		final XstsCombinedExprTraceChecker traceChecker = createTraceChecker(initFormula, negProp, lazyToConcrProd2Lens);
		final XstsCombinedPrecRefiner precRefiner = createPrecRefiner(xsts);

		final Refiner refiner;
		if (refinement == XstsConfigBuilder.Refinement.MULTI_SEQ) {
			refiner = MultiExprTraceRefiner.create(traceChecker, precRefiner, pruneStrategy, logger);
		} else {
			refiner = SingleExprTraceRefiner.create(traceChecker, precRefiner, pruneStrategy, logger);
		}

		if (domain == XstsConfigBuilder.Domain.EXPL) {

			final LazyStrategy lazyDataStrategy = new BasicLazyStrategy<>(
					XstsLazyLensUtils.createConcrDataLens(),
					BasicConcretizer.create(ExplOrd.getInstance())
			);

			final Function<LazyState<XstsState<Prod2State<ExplState, ZoneState>>, XstsState<Prod2State<ExplState, ZoneState>>>, ?> projection = s -> Tuple4.of(
					s.getAbstrState().isInitialized(),
					s.getAbstrState().lastActionWasEnv(),
					lazyDataStrategy.getProjection().apply(s),
					lazyClockStrategy.getProjection().apply(s)
			);

			final Prod2LazyStrategy lazyStrategy = new Prod2LazyStrategy<>(lazyToConcrProd2Lens, lazyDataStrategy, lazyClockStrategy, projection);

			final TimedXstsProd2Analysis splitProd2Analysis = TimedXstsProd2Analysis.create(
					ExplStmtAnalysis.create(abstractionSolver, initFormula, maxEnum),
					ZoneStmtAnalysis.getInstance(),
					timedXstsActionProjections
			);

			final XstsAnalysis<Prod2State<ExplState, ZoneState>, Prod2Prec<ExplPrec, ZonePrec>> xstsAnalysis =
					XstsAnalysis.create(splitProd2Analysis);

			final LazyAnalysis lazyAnalysis = LazyAnalysis.create(
					XstsOrd.create(lazyStrategy.getPartialOrd()),
					xstsAnalysis.getInitFunc(),
					xstsAnalysis.getTransFunc(),
					XstsInitAbstractor.create(lazyStrategy.getInitAbstractor())
			);

			final Predicate<ExplState> dataTarget = new ExplStatePredicate(negProp, abstractionSolver);
			final Predicate<Prod2State<ExplState, ZoneState>> prod2Target = s -> dataTarget.test(s.getState1());
			final Predicate<XstsState> target = new XstsStatePredicate(prod2Target);

			final XstsStmtOptimizer<Prod2State<ExplState, ZoneState>> stmtOptimizer;
			if (optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer =
						XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
								ExplStmtOptimizer.getInstance(),
								DefaultStmtOptimizer.create()
						));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (clockStrategy.controlFlowSplitting) {
				final Solver cfSplitSolver = solverFactory.createSolver();
				final ValuationExtractor<Prod2State<ExplState, ZoneState>> valExtractor =
						createDataValExtractor(ExplStateValuationExtractor.getInstance());
				final ControlFlowSplitXstsLts<Prod2State<ExplState, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new ControlFlowSplitLazyAbstractor(lts, search.strategy, lazyStrategy, lazyAnalysis, target, clockStrategy.filterInfeasibleCF);
			} else {
				final LTS<XstsState<Prod2State<ExplState, ZoneState>>, XstsAction> lts = XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor(lts, search.strategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<ExplState, ZoneState>>, XstsAction, Prod2Prec<ExplPrec, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, logger);
			final Prod2Prec<ExplPrec, ZonePrec> prec = Prod2Prec.of(initPrec.builder.createExpl(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else if (domain == XstsConfigBuilder.Domain.PRED_BOOL || domain == XstsConfigBuilder.Domain.PRED_CART || domain == XstsConfigBuilder.Domain.PRED_SPLIT) {

			final LazyStrategy lazyDataStrategy = new BasicLazyStrategy<>(
					XstsLazyLensUtils.createConcrDataLens(),
					BasicConcretizer.create(PredOrd.create(abstractionSolver))
			);

			final Function<LazyState<XstsState<Prod2State<PredState, ZoneState>>, XstsState<Prod2State<PredState, ZoneState>>>, ?> projection = s -> Tuple4.of(
					s.getAbstrState().isInitialized(),
					s.getAbstrState().lastActionWasEnv(),
					lazyDataStrategy.getProjection().apply(s),
					lazyClockStrategy.getProjection().apply(s)
			);

			final Prod2LazyStrategy lazyStrategy = new Prod2LazyStrategy<>(lazyToConcrProd2Lens, lazyDataStrategy, lazyClockStrategy, projection);

			PredAbstractors.PredAbstractor predAbstractor = switch (domain) {
				case PRED_BOOL -> PredAbstractors.booleanAbstractor(abstractionSolver);
				case PRED_SPLIT -> PredAbstractors.booleanSplitAbstractor(abstractionSolver);
				case PRED_CART -> PredAbstractors.cartesianAbstractor(abstractionSolver);
				default -> throw new UnsupportedOperationException(domain + " domain is not supported.");
			};

			final TimedXstsProd2Analysis splitProd2Analysis = TimedXstsProd2Analysis.create(
					PredAnalysis.create(abstractionSolver, predAbstractor, initFormula),
					ZoneStmtAnalysis.getInstance(),
					timedXstsActionProjections
			);

			final XstsAnalysis<Prod2State<PredState, ZoneState>, Prod2Prec<PredPrec, ZonePrec>> xstsAnalysis =
					XstsAnalysis.create(splitProd2Analysis);

			final LazyAnalysis lazyAnalysis = LazyAnalysis.create(
					XstsOrd.create(lazyStrategy.getPartialOrd()),
					xstsAnalysis.getInitFunc(),
					xstsAnalysis.getTransFunc(),
					XstsInitAbstractor.create(lazyStrategy.getInitAbstractor())
			);

			final Predicate<ExprState> dataTarget = new ExprStatePredicate(negProp, abstractionSolver);
			final Predicate<Prod2State<PredState, ZoneState>> prod2Target = s -> dataTarget.test(s.getState1());
			final Predicate<XstsState<Prod2State<PredState, ZoneState>>> target = new XstsStatePredicate<>(prod2Target);

			final XstsStmtOptimizer<Prod2State<PredState, ZoneState>> stmtOptimizer;
			if (optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer = XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
						PredStmtOptimizer.getInstance(),
						DefaultStmtOptimizer.create()));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (clockStrategy.controlFlowSplitting) {
				final Solver cfSplitSolver = solverFactory.createSolver();
				final ValuationExtractor<Prod2State<PredState, ZoneState>> valExtractor =
						createDataValExtractor(PredStateValuationExtractor.getInstance());
				final ControlFlowSplitXstsLts<Prod2State<PredState, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new ControlFlowSplitLazyAbstractor(lts, search.strategy, lazyStrategy, lazyAnalysis, target, clockStrategy.filterInfeasibleCF);
			} else {
				final LTS<XstsState<Prod2State<PredState, ZoneState>>, XstsAction> lts = XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor<>(lts, search.strategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<PredState, ZoneState>>, XstsAction, Prod2Prec<PredPrec, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, logger);
			final Prod2Prec<PredPrec, ZonePrec> prec = Prod2Prec.of(initPrec.builder.createPred(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else if (domain == XstsConfigBuilder.Domain.EXPL_PRED_BOOL || domain == XstsConfigBuilder.Domain.EXPL_PRED_CART || domain == XstsConfigBuilder.Domain.EXPL_PRED_COMBINED || domain == XstsConfigBuilder.Domain.EXPL_PRED_SPLIT) {

			final LazyStrategy lazyDataStrategy = new BasicLazyStrategy<>(
					XstsLazyLensUtils.createConcrDataLens(),
					BasicConcretizer.create(Prod2Ord.create(ExplOrd.getInstance(), PredOrd.create(abstractionSolver)))
			);

			final Function<LazyState<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>, XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>>, ?>
					projection = s -> Tuple4.of(
							s.getAbstrState().isInitialized(),
							s.getAbstrState().lastActionWasEnv(),
							lazyDataStrategy.getProjection().apply(s),
							lazyClockStrategy.getProjection().apply(s)
					);

			final Prod2LazyStrategy lazyStrategy = new Prod2LazyStrategy<>(lazyToConcrProd2Lens, lazyDataStrategy, lazyClockStrategy, projection);

			final Analysis<Prod2State<ExplState, PredState>, StmtAction, Prod2Prec<ExplPrec, PredPrec>> dataAnalysis;

			if (domain == XstsConfigBuilder.Domain.EXPL_PRED_BOOL || domain == XstsConfigBuilder.Domain.EXPL_PRED_CART || domain == XstsConfigBuilder.Domain.EXPL_PRED_SPLIT) {
				final PredAbstractors.PredAbstractor predAbstractor = switch (domain) {
					case EXPL_PRED_BOOL -> PredAbstractors.booleanAbstractor(abstractionSolver);
					case EXPL_PRED_SPLIT -> PredAbstractors.booleanSplitAbstractor(abstractionSolver);
					case EXPL_PRED_CART -> PredAbstractors.cartesianAbstractor(abstractionSolver);
					default -> throw new UnsupportedOperationException(domain + " domain is not supported.");
				};
				dataAnalysis = Prod2Analysis.create(
						ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), maxEnum),
						PredAnalysis.create(abstractionSolver, predAbstractor, xsts.getInitFormula()),
						Prod2ExplPredPreStrengtheningOperator.create(),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolver));
			} else {
				final Prod2ExplPredAbstractors.Prod2ExplPredAbstractor prodAbstractor = Prod2ExplPredAbstractors.booleanAbstractor(abstractionSolver);
				dataAnalysis = Prod2ExplPredAnalysis.create(
						ExplAnalysis.create(abstractionSolver, xsts.getInitFormula()),
						PredAnalysis.create(abstractionSolver, PredAbstractors.booleanAbstractor(abstractionSolver), xsts.getInitFormula()),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolver),
						prodAbstractor);
			}

			final TimedXstsProd2Analysis splitProd2Analysis = TimedXstsProd2Analysis.create(
					dataAnalysis, ZoneStmtAnalysis.getInstance(), timedXstsActionProjections
			);

			final XstsAnalysis<Prod2State<Prod2State<ExplState, PredState>, ZoneState>, Prod2Prec<Prod2Prec<ExplPrec, PredPrec>, ZonePrec>>
					xstsAnalysis = XstsAnalysis.create(splitProd2Analysis);

			final LazyAnalysis lazyAnalysis = LazyAnalysis.create(
					XstsOrd.create(lazyStrategy.getPartialOrd()),
					xstsAnalysis.getInitFunc(),
					xstsAnalysis.getTransFunc(),
					XstsInitAbstractor.create(lazyStrategy.getInitAbstractor())
			);

			final Predicate<ExprState> dataTarget = new ExprStatePredicate(negProp, abstractionSolver);
			final Predicate<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> prod2Target = s -> dataTarget.test(s.getState1());
			final Predicate<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>> target = new XstsStatePredicate<>(prod2Target);

			final XstsStmtOptimizer<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> stmtOptimizer;
			if (optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer = XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
						Prod2ExplPredStmtOptimizer.create(ExplStmtOptimizer.getInstance()),
						DefaultStmtOptimizer.create()));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (clockStrategy.controlFlowSplitting) {
				final Solver cfSplitSolver = solverFactory.createSolver();
				final ValuationExtractor<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> valExtractor =
						createDataValExtractor(Prod2ExplPredStateValuationExtractor.create(ExplStateValuationExtractor.getInstance()));
				final ControlFlowSplitXstsLts<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new ControlFlowSplitLazyAbstractor(lts, search.strategy, lazyStrategy, lazyAnalysis, target, clockStrategy.filterInfeasibleCF);
			} else {
				final LTS<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>, XstsAction> lts =
						XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor<>(lts, search.strategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>, XstsAction, Prod2Prec<Prod2Prec<ExplPrec, PredPrec>, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, logger);
			final Prod2Prec<Prod2Prec<ExplPrec, PredPrec>, ZonePrec> prec = Prod2Prec.of(initPrec.builder.createProd2ExplPred(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else {
			throw new UnsupportedOperationException(domain + " domain is not supported.");
		}
	}

	private <SData extends State> ValuationExtractor<Prod2State<SData, ZoneState>> createDataValExtractor(final ValuationExtractor<SData> dataValExtractor) {
		return new ValuationExtractor<>() {
			@Override
			public Valuation extractValuation(Prod2State<SData, ZoneState> state) {
				return dataValExtractor.extractValuation(state.getState1());
			}
			@Override
			public Valuation extractValuationForVars(Prod2State<SData, ZoneState> state, Collection<VarDecl<?>> vars) {
				return dataValExtractor.extractValuationForVars(state.getState1(), vars);
			}
		};
	}

	private LazyStrategy<ZoneState, ZoneState, LazyState<XstsState<Prod2State<?, ZoneState>>, XstsState<Prod2State<?, ZoneState>>>, XstsAction>
	createLazyZoneStrategy(final ZonePrec zonePrec) {
		final Lens<LazyState<XstsState<Prod2State<?, ZoneState>>, XstsState<Prod2State<?, ZoneState>>>, LazyState<ZoneState, ZoneState>>
				lens = XstsLazyLensUtils.createLazyClockLens();
		final Lattice<ZoneState> lattice = ZoneLattice.getInstance();
		final Interpolator<ZoneState, ZoneState> interpolator = ZoneInterpolator.getInstance();
		final PartialOrd<ZoneState> partialOrd = ZoneOrd.getInstance();
		final Concretizer<ZoneState, ZoneState> concretizer = BasicConcretizer.create(partialOrd);
		final InvTransFunc<ZoneState, XstsAction, ZonePrec> xstsZoneInvTransFunc = (state, action, prec) ->
				ZoneStmtInvTransFunc.getInstance().getPreStates(state, timedXstsActionProjections.clockProjection(action), prec);

		switch (zoneRefinement) {
			case BW_ITP:
				return new BwItpStrategy<>(lens, lattice, interpolator, concretizer, xstsZoneInvTransFunc, zonePrec);
			case FW_ITP:
				final TransFunc<ZoneState, XstsAction, ZonePrec> xstsZoneTransFunc = (state, action, prec) ->
						ZoneStmtTransFunc.getInstance().getSuccStates(state, timedXstsActionProjections.clockProjection(action), prec);
				return new FwItpStrategy<>(lens, lattice, interpolator, concretizer, xstsZoneInvTransFunc, zonePrec, xstsZoneTransFunc, zonePrec);
			default:
				throw new AssertionError();
		}
	}

	private XstsCombinedExprTraceChecker createTraceChecker(final Expr<BoolType> initFormula, final Expr<BoolType> negProp,
															final Lens lens) {
		final XstsCombinedExprTraceChecker traceChecker = new XstsCombinedExprTraceChecker(
				switch (refinement) {
					case FW_BIN_ITP -> ExprTraceFwBinItpChecker.create(initFormula, negProp, solverFactory.createItpSolver());
					case BW_BIN_ITP -> ExprTraceBwBinItpChecker.create(initFormula, negProp, solverFactory.createItpSolver());
					case SEQ_ITP, MULTI_SEQ -> ExprTraceSeqItpChecker.create(initFormula, negProp, solverFactory.createItpSolver());
					case UNSAT_CORE -> ExprTraceUnsatCoreChecker.create(initFormula, negProp, solverFactory.createUCSolver());
				}, lens, timedXstsActionProjections);
		return traceChecker;
	}

	private XstsCombinedPrecRefiner createPrecRefiner(final XSTS xsts) {
		final XstsCombinedPrecRefiner precRefiner = new XstsCombinedPrecRefiner(
				switch (domain) {
					case EXPL -> new ItpRefToExplPrec();
					case PRED_BOOL, PRED_CART, PRED_SPLIT -> new ItpRefToPredPrec(predSplit.splitter);
					case EXPL_PRED_BOOL, EXPL_PRED_CART, EXPL_PRED_COMBINED, EXPL_PRED_SPLIT ->
							AutomaticItpRefToProd2ExplPredPrec.create(autoExpl.builder.create(xsts), predSplit.splitter);
				});
		return precRefiner;
	}
}
