package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.ItpRefToProd2ExplPredPrec;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredPreStrengtheningOperator;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredStrengtheningOperator;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsCtrlInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsEmptyInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsPropInitPrec;

import java.util.Set;
import java.util.function.Predicate;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class XstsConfigBuilder {

	public enum Domain {
		EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT, PROD
	}

	public enum Refinement {
		FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE
	}

	public enum Search {
		BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),

		DFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

		public final ArgNodeComparators.ArgNodeComparator comparator;

		private Search(final ArgNodeComparators.ArgNodeComparator comparator) {
			this.comparator = comparator;
		}

	}

	public enum PredSplit {
		WHOLE(ExprSplitters.whole()),

		CONJUNCTS(ExprSplitters.conjuncts()),

		ATOMS(ExprSplitters.atoms());

		public final ExprSplitters.ExprSplitter splitter;

		private PredSplit(final ExprSplitters.ExprSplitter splitter) {
			this.splitter = splitter;
		}
	}

	public enum InitPrec {
		EMPTY(new XstsEmptyInitPrec()),

		PROP(new XstsPropInitPrec()),

		CTRL(new XstsCtrlInitPrec());

		public final XstsInitPrec builder;

		private InitPrec(final XstsInitPrec builder) {
			this.builder = builder;
		}

	}

	private Logger logger = NullLogger.getInstance();
	private final SolverFactory solverFactory;
	private final Domain domain;
	private final Refinement refinement;
	private Search search = Search.BFS;
	private PredSplit predSplit = PredSplit.WHOLE;
	private int maxEnum = 0;
	private InitPrec initPrec = InitPrec.EMPTY;
	private PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	public XstsConfigBuilder(final Domain domain, final Refinement refinement, final SolverFactory solverFactory) {
		this.domain = domain;
		this.refinement = refinement;
		this.solverFactory = solverFactory;
	}

	public XstsConfigBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public XstsConfigBuilder search(final Search search) {
		this.search = search;
		return this;
	}

	public XstsConfigBuilder predSplit(final PredSplit predSplit) {
		this.predSplit = predSplit;
		return this;
	}

	public XstsConfigBuilder maxEnum(final int maxEnum) {
		this.maxEnum = maxEnum;
		return this;
	}

	public XstsConfigBuilder initPrec(final InitPrec initPrec) {
		this.initPrec = initPrec;
		return this;
	}

	public XstsConfigBuilder pruneStrategy(final PruneStrategy pruneStrategy) {
		this.pruneStrategy = pruneStrategy;
		return this;
	}

	public XstsConfig<? extends State, ? extends Action, ? extends Prec> build(final XSTS xsts) {
		final ItpSolver solver = solverFactory.createItpSolver();
		LTS<XstsState, XstsAction> lts = XstsLts.create(xsts);
		final Expr<BoolType> negProp = Not(xsts.getProp());

		if (domain == Domain.EXPL) {
			final Predicate<XstsState<ExplState>> target = new XstsStatePredicate<ExplStatePredicate, ExplState>(new ExplStatePredicate(negProp, solver));
			final Analysis<XstsState<ExplState>, XstsAction, ExplPrec> analysis = XstsAnalysis.create(ExplStmtAnalysis.create(solver, xsts.getInitFormula(), maxEnum));
			final ArgBuilder<XstsState<ExplState>, XstsAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis, target,
					true);
			final Abstractor<XstsState<ExplState>, XstsAction, ExplPrec> abstractor = BasicAbstractor.builder(argBuilder)
					.waitlist(PriorityWaitlist.create(search.comparator))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex())
					.logger(logger).build();

			Refiner<XstsState<ExplState>, XstsAction, ExplPrec> refiner = null;

			switch (refinement) {
				case FW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case BW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case SEQ_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case MULTI_SEQ:
					refiner = MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case UNSAT_CORE:
					refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(new VarsRefToExplPrec()), pruneStrategy, logger);
					break;
				default:
					throw new UnsupportedOperationException(domain + " domain does not support " + refinement + " refinement.");
			}

			final SafetyChecker<XstsState<ExplState>, XstsAction, ExplPrec> checker = CegarChecker.create(abstractor, refiner,
					logger);
			final ExplPrec prec = initPrec.builder.createExpl(xsts);
			return XstsConfig.create(checker, prec);

		} else if (domain == Domain.PRED_BOOL || domain == Domain.PRED_CART || domain == Domain.PRED_SPLIT) {
			PredAbstractors.PredAbstractor predAbstractor = null;
			switch (domain) {
				case PRED_BOOL:
					predAbstractor = PredAbstractors.booleanAbstractor(solver);
					break;
				case PRED_SPLIT:
					predAbstractor = PredAbstractors.booleanSplitAbstractor(solver);
					break;
				case PRED_CART:
					predAbstractor = PredAbstractors.cartesianAbstractor(solver);
					break;
				default:
					throw new UnsupportedOperationException(domain + " domain is not supported.");
			}
			final Predicate<XstsState<PredState>> target = new XstsStatePredicate<ExprStatePredicate, PredState>(new ExprStatePredicate(negProp, solver));
			final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis = XstsAnalysis.create(PredAnalysis.create(solver, predAbstractor,
					xsts.getInitFormula()));
			final ArgBuilder<XstsState<PredState>, XstsAction, PredPrec> argBuilder = ArgBuilder.create(lts, analysis, target,
					true);
			final Abstractor<XstsState<PredState>, XstsAction, PredPrec> abstractor = BasicAbstractor.builder(argBuilder)
					.waitlist(PriorityWaitlist.create(search.comparator))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex())
					.logger(logger).build();

			ExprTraceChecker<ItpRefutation> exprTraceChecker = null;
			switch (refinement) {
				case FW_BIN_ITP:
					exprTraceChecker = ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solver);
					break;
				case BW_BIN_ITP:
					exprTraceChecker = ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solver);
					break;
				case SEQ_ITP:
					exprTraceChecker = ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver);
					break;
				case MULTI_SEQ:
					exprTraceChecker = ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver);
					break;
				default:
					throw new UnsupportedOperationException(
							domain + " domain does not support " + refinement + " refinement.");
			}
			Refiner<XstsState<PredState>, XstsAction, PredPrec> refiner;
			if (refinement == Refinement.MULTI_SEQ) {
				refiner = MultiExprTraceRefiner.create(exprTraceChecker,
						JoiningPrecRefiner.create(new ItpRefToPredPrec(predSplit.splitter)), pruneStrategy, logger);
			} else {
				refiner = SingleExprTraceRefiner.create(exprTraceChecker,
						JoiningPrecRefiner.create(new ItpRefToPredPrec(predSplit.splitter)), pruneStrategy, logger);
			}

			final SafetyChecker<XstsState<PredState>, XstsAction, PredPrec> checker = CegarChecker.create(abstractor, refiner,
					logger);

			final PredPrec prec = initPrec.builder.createPred(xsts);
			return XstsConfig.create(checker, prec);
		} else if (domain == Domain.PROD) {
			final PredAbstractors.PredAbstractor predAbstractor = PredAbstractors.cartesianAbstractor(solver);
			final Predicate<XstsState<Prod2State<ExplState, PredState>>> target = new XstsStatePredicate<ExprStatePredicate, Prod2State<ExplState, PredState>>(new ExprStatePredicate(negProp, solver));
			final Analysis<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> analysis
					= XstsAnalysis.create(Prod2Analysis.create(
					ExplStmtAnalysis.create(solver, xsts.getInitFormula(), maxEnum),
					PredAnalysis.create(solver, predAbstractor, xsts.getInitFormula()),
					Prod2ExplPredPreStrengtheningOperator.create(),
					Prod2ExplPredStrengtheningOperator.create(solver)));
			final ArgBuilder<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> argBuilder = ArgBuilder.create(lts, analysis, target,
					true);
			final Abstractor<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> abstractor = BasicAbstractor.builder(argBuilder)
					.waitlist(PriorityWaitlist.create(search.comparator))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex())
					.logger(logger).build();

			Refiner<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> refiner = null;

			final Set<VarDecl<?>> ctrlVars = xsts.getCtrlVars();
			switch (refinement) {
				case FW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(ItpRefToProd2ExplPredPrec.create(ctrlVars, predSplit.splitter)), pruneStrategy, logger);
					break;
				case BW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(ItpRefToProd2ExplPredPrec.create(ctrlVars, predSplit.splitter)), pruneStrategy, logger);
					break;
				case SEQ_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(ItpRefToProd2ExplPredPrec.create(ctrlVars, predSplit.splitter)), pruneStrategy, logger);
					break;
				case MULTI_SEQ:
					refiner = MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solver),
							JoiningPrecRefiner.create(ItpRefToProd2ExplPredPrec.create(ctrlVars, predSplit.splitter)), pruneStrategy, logger);
					break;
				default:
					throw new UnsupportedOperationException(
							domain + " domain does not support " + refinement + " refinement.");
			}

			final SafetyChecker<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> checker = CegarChecker.create(abstractor, refiner,
					logger);
			final Prod2Prec<ExplPrec, PredPrec> prec = initPrec.builder.createProd2ExplPred(xsts);
			return XstsConfig.create(checker, prec);
		} else {
			throw new UnsupportedOperationException(domain + " domain is not supported.");
		}
	}


}
