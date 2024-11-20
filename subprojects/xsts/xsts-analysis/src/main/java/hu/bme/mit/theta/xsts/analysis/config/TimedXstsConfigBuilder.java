package hu.bme.mit.theta.xsts.analysis.config;

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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.clocktype.ClockType;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.timed.XstsCombinedExprTraceChecker;
import hu.bme.mit.theta.xsts.analysis.timed.XstsCombinedPrecRefiner;
import hu.bme.mit.theta.xsts.analysis.timed.*;

import java.util.Collection;
import java.util.function.Function;
import java.util.function.Predicate;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

@SuppressWarnings({"rawtypes", "unchecked"})
public final class TimedXstsConfigBuilder {

	public enum ZoneRefinement {
		BW_ITP, FW_ITP
	}

	public enum ControlFlowSplitting {

		OFF(false, false),

		ALL_ACTIONS(true, false),

		FEASIBLE_ACTIONS_ONLY(true, true);

		public final boolean controlFlowSplitting;
		public final boolean feasibleActionsOnly;

		ControlFlowSplitting(final boolean controlFlowSplitting, final boolean feasibleActionsOnly) {
			this.controlFlowSplitting = controlFlowSplitting;
			this.feasibleActionsOnly = feasibleActionsOnly;
		}
	}

	private final XstsConfigBuilder xstsConfig;
	private final SearchStrategy searchStrategy;
	private ZoneRefinement zoneRefinement = ZoneRefinement.BW_ITP;
	private TimedXstsActionProjections timedXstsActionProjections;
	private ControlFlowSplitting controlFlowSplitting = ControlFlowSplitting.OFF;

	public TimedXstsConfigBuilder(final XstsConfigBuilder xstsConfig) {
		this.xstsConfig = xstsConfig;
		this.searchStrategy = switch (xstsConfig.search) {
			case BFS -> SearchStrategy.BFS;
			case DFS -> SearchStrategy.DFS;
		};
	}

	public TimedXstsConfigBuilder zoneRefinement(final ZoneRefinement zoneRefinement) {
		this.zoneRefinement = zoneRefinement;
		return this;
	}
	
	public TimedXstsConfigBuilder controlFlowSplitting(final ControlFlowSplitting controlFlowSplitting) {
		this.controlFlowSplitting = controlFlowSplitting;
		return this;
	}

	public XstsConfig<? extends State, ? extends Action, ? extends Prec> build(XSTS xsts) {
		final Solver abstractionSolver = xstsConfig.solverFactory.createSolver();

		timedXstsActionProjections = TimedXstsActionProjections.create();

		xsts = xstsConfig.clockReplacer.clockReplacer.apply(xsts);

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
		if (xstsConfig.refinement == XstsConfigBuilder.Refinement.MULTI_SEQ) {
			refiner = MultiExprTraceRefiner.create(traceChecker, precRefiner, xstsConfig.pruneStrategy, xstsConfig.logger);
		} else {
			refiner = SingleExprTraceRefiner.create(traceChecker, precRefiner, xstsConfig.pruneStrategy, xstsConfig.logger);
		}

		if (xstsConfig.domain == XstsConfigBuilder.Domain.EXPL) {

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
					ExplStmtAnalysis.create(abstractionSolver, initFormula, xstsConfig.maxEnum),
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
			if (xstsConfig.optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer =
						XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
								ExplStmtOptimizer.getInstance(),
								DefaultStmtOptimizer.create()
						));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (controlFlowSplitting.controlFlowSplitting) {
				final Solver cfSplitSolver = xstsConfig.solverFactory.createSolver();
				final ValuationExtractor<Prod2State<ExplState, ZoneState>> valExtractor =
						createDataValExtractor(ExplStateValuationExtractor.getInstance());
				final ControlFlowSplitXstsLts<Prod2State<ExplState, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new XstsLazyAbstractor(lts, searchStrategy, lazyStrategy, lazyAnalysis, target, controlFlowSplitting.feasibleActionsOnly);
			} else {
				final LTS<XstsState<Prod2State<ExplState, ZoneState>>, XstsAction> lts = XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor(lts, searchStrategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<ExplState, ZoneState>>, XstsAction, Prod2Prec<ExplPrec, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, xstsConfig.logger);
			final Prod2Prec<ExplPrec, ZonePrec> prec = Prod2Prec.of(xstsConfig.initPrec.builder.createExpl(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else if (xstsConfig.domain == XstsConfigBuilder.Domain.PRED_BOOL || xstsConfig.domain == XstsConfigBuilder.Domain.PRED_CART || xstsConfig.domain == XstsConfigBuilder.Domain.PRED_SPLIT) {

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

			PredAbstractors.PredAbstractor predAbstractor = switch (xstsConfig.domain) {
				case PRED_BOOL -> PredAbstractors.booleanAbstractor(abstractionSolver);
				case PRED_SPLIT -> PredAbstractors.booleanSplitAbstractor(abstractionSolver);
				case PRED_CART -> PredAbstractors.cartesianAbstractor(abstractionSolver);
				default -> throw new UnsupportedOperationException(xstsConfig.domain + " domain is not supported.");
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
			if (xstsConfig.optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer = XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
						PredStmtOptimizer.getInstance(),
						DefaultStmtOptimizer.create()));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (controlFlowSplitting != ControlFlowSplitting.OFF) {
				final Solver cfSplitSolver = xstsConfig.solverFactory.createSolver();
				final ValuationExtractor<Prod2State<PredState, ZoneState>> valExtractor =
						createDataValExtractor(PredStateValuationExtractor.getInstance());
				final ControlFlowSplitXstsLts<Prod2State<PredState, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new XstsLazyAbstractor(lts, searchStrategy, lazyStrategy, lazyAnalysis, target, controlFlowSplitting.feasibleActionsOnly);
			} else {
				final LTS<XstsState<Prod2State<PredState, ZoneState>>, XstsAction> lts = XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor<>(lts, searchStrategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<PredState, ZoneState>>, XstsAction, Prod2Prec<PredPrec, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, xstsConfig.logger);
			final Prod2Prec<PredPrec, ZonePrec> prec = Prod2Prec.of(xstsConfig.initPrec.builder.createPred(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else if (xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_BOOL || xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_CART || xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_COMBINED || xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_SPLIT) {

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

			if (xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_BOOL || xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_CART || xstsConfig.domain == XstsConfigBuilder.Domain.EXPL_PRED_SPLIT) {
				final PredAbstractors.PredAbstractor predAbstractor = switch (xstsConfig.domain) {
					case EXPL_PRED_BOOL -> PredAbstractors.booleanAbstractor(abstractionSolver);
					case EXPL_PRED_SPLIT -> PredAbstractors.booleanSplitAbstractor(abstractionSolver);
					case EXPL_PRED_CART -> PredAbstractors.cartesianAbstractor(abstractionSolver);
					default -> throw new UnsupportedOperationException(xstsConfig.domain + " domain is not supported.");
				};
				dataAnalysis = Prod2Analysis.create(
						ExplStmtAnalysis.create(abstractionSolver, initFormula, xstsConfig.maxEnum),
						PredAnalysis.create(abstractionSolver, predAbstractor, initFormula),
						Prod2ExplPredPreStrengtheningOperator.create(),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolver));
			} else {
				final Prod2ExplPredAbstractors.Prod2ExplPredAbstractor prodAbstractor = Prod2ExplPredAbstractors.booleanAbstractor(abstractionSolver);
				dataAnalysis = Prod2ExplPredAnalysis.create(
						ExplAnalysis.create(abstractionSolver, initFormula),
						PredAnalysis.create(abstractionSolver, PredAbstractors.booleanAbstractor(abstractionSolver), initFormula),
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
			if (xstsConfig.optimizeStmts == XstsConfigBuilder.OptimizeStmts.ON) {
				stmtOptimizer = XstsStmtOptimizer.create(Prod2StmtOptimizer.create(
						Prod2ExplPredStmtOptimizer.create(ExplStmtOptimizer.getInstance()),
						DefaultStmtOptimizer.create()));
			} else {
				stmtOptimizer = XstsStmtOptimizer.create(DefaultStmtOptimizer.create());
			}

			final Abstractor abstractor;
			if (controlFlowSplitting != ControlFlowSplitting.OFF) {
				final Solver cfSplitSolver = xstsConfig.solverFactory.createSolver();
				final ValuationExtractor<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> valExtractor =
						createDataValExtractor(Prod2ExplPredStateValuationExtractor.create(ExplStateValuationExtractor.getInstance()));
				final ControlFlowSplitXstsLts<Prod2State<Prod2State<ExplState, PredState>, ZoneState>> lts =
						ControlFlowSplitXstsLts.create(xsts, cfSplitSolver, valExtractor);
				abstractor = new XstsLazyAbstractor(lts, searchStrategy, lazyStrategy, lazyAnalysis, target, controlFlowSplitting.feasibleActionsOnly);
			} else {
				final LTS<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>, XstsAction> lts =
						XstsLts.create(xsts, stmtOptimizer);
				abstractor = new LazyAbstractor<>(lts, searchStrategy, lazyStrategy, lazyAnalysis, target);
			}

			final SafetyChecker<XstsState<Prod2State<Prod2State<ExplState, PredState>, ZoneState>>, XstsAction, Prod2Prec<Prod2Prec<ExplPrec, PredPrec>, ZonePrec>>
					checker = CegarChecker.create(abstractor, refiner, xstsConfig.logger);
			final Prod2Prec<Prod2Prec<ExplPrec, PredPrec>, ZonePrec> prec = Prod2Prec.of(xstsConfig.initPrec.builder.createProd2ExplPred(xsts), zonePrec);
			return XstsConfig.create(checker, prec);

		} else {
			throw new UnsupportedOperationException(xstsConfig.domain + " domain is not supported.");
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
				switch (xstsConfig.refinement) {
					case FW_BIN_ITP -> ExprTraceFwBinItpChecker.create(initFormula, negProp, xstsConfig.solverFactory.createItpSolver());
					case BW_BIN_ITP -> ExprTraceBwBinItpChecker.create(initFormula, negProp, xstsConfig.solverFactory.createItpSolver());
					case SEQ_ITP, MULTI_SEQ -> ExprTraceSeqItpChecker.create(initFormula, negProp, xstsConfig.solverFactory.createItpSolver());
					case UNSAT_CORE -> ExprTraceUnsatCoreChecker.create(initFormula, negProp, xstsConfig.solverFactory.createUCSolver());
				}, lens, timedXstsActionProjections);
		return traceChecker;
	}

	private XstsCombinedPrecRefiner createPrecRefiner(final XSTS xsts) {
		final XstsCombinedPrecRefiner precRefiner = new XstsCombinedPrecRefiner(
				switch (xstsConfig.domain) {
					case EXPL -> new ItpRefToExplPrec();
					case PRED_BOOL, PRED_CART, PRED_SPLIT -> new ItpRefToPredPrec(xstsConfig.predSplit.splitter);
					case EXPL_PRED_BOOL, EXPL_PRED_CART, EXPL_PRED_COMBINED, EXPL_PRED_SPLIT ->
							AutomaticItpRefToProd2ExplPredPrec.create(xstsConfig.autoExpl.builder.create(xsts), xstsConfig.predSplit.splitter);
				});
		return precRefiner;
	}
}
