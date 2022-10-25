/*
 *  Copyright 2022 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStatePredicate;
import hu.bme.mit.theta.analysis.expl.ExplStmtAnalysis;
import hu.bme.mit.theta.analysis.expl.ExplStmtOptimizer;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.JoiningPrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.MultiExprTraceRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.PredStmtOptimizer;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.*;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsAction;
import hu.bme.mit.theta.xsts.analysis.XstsAnalysis;
import hu.bme.mit.theta.xsts.analysis.XstsLts;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import hu.bme.mit.theta.xsts.analysis.XstsStatePredicate;
import hu.bme.mit.theta.xsts.analysis.XstsStmtOptimizer;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsNewAtomsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsNewOperandsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsStaticAutoExpl;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsAllVarsInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsCtrlInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsEmptyInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsPropInitPrec;

import java.util.Set;
import java.util.function.Predicate;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

public class XstsConfigBuilder {

	public enum Domain {
		EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT, EXPL_PRED_BOOL, EXPL_PRED_CART, EXPL_PRED_SPLIT, EXPL_PRED_COMBINED
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

		CTRL(new XstsCtrlInitPrec()),

		ALLVARS(new XstsAllVarsInitPrec());

		public final XstsInitPrec builder;

		private InitPrec(final XstsInitPrec builder) {
			this.builder = builder;
		}

	}

	public enum AutoExpl {
		STATIC(new XstsStaticAutoExpl()),

		NEWATOMS(new XstsNewAtomsAutoExpl()),

		NEWOPERANDS(new XstsNewOperandsAutoExpl());

		public final XstsAutoExpl builder;

		private AutoExpl(final XstsAutoExpl builder) { this.builder = builder; }
	}

	public enum OptimizeStmts {
		ON, OFF
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
	private OptimizeStmts optimizeStmts = OptimizeStmts.ON;
	private AutoExpl autoExpl = AutoExpl.NEWOPERANDS;

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

	public XstsConfigBuilder optimizeStmts(final OptimizeStmts optimizeStmts) {
		this.optimizeStmts = optimizeStmts;
		return this;
	}

	public XstsConfigBuilder autoExpl(final AutoExpl autoExpl) {
		this.autoExpl = autoExpl;
		return this;
	}

	public XstsConfig<? extends State, ? extends Action, ? extends Prec> build(final XSTS xsts) {
		final Solver abstractionSolver = solverFactory.createSolver();
		final Expr<BoolType> negProp = Not(xsts.getProp());

		if (domain == Domain.EXPL) {
			final LTS<XstsState<ExplState>, XstsAction> lts;
			if(optimizeStmts == OptimizeStmts.ON){
				lts = XstsLts.create(xsts, XstsStmtOptimizer.create(ExplStmtOptimizer.getInstance()));
			} else {
				lts = XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
			}

			final Predicate<XstsState<ExplState>> target = new XstsStatePredicate<ExplStatePredicate, ExplState>(new ExplStatePredicate(negProp, abstractionSolver));
			final Analysis<XstsState<ExplState>, XstsAction, ExplPrec> analysis = XstsAnalysis.create(ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), maxEnum));
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
					refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case BW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case SEQ_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case MULTI_SEQ:
					refiner = MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case UNSAT_CORE:
					refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(xsts.getInitFormula(), negProp, solverFactory.createUCSolver()),
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
					predAbstractor = PredAbstractors.booleanAbstractor(abstractionSolver);
					break;
				case PRED_SPLIT:
					predAbstractor = PredAbstractors.booleanSplitAbstractor(abstractionSolver);
					break;
				case PRED_CART:
					predAbstractor = PredAbstractors.cartesianAbstractor(abstractionSolver);
					break;
				default:
					throw new UnsupportedOperationException(domain + " domain is not supported.");
			}

			final LTS<XstsState<PredState>, XstsAction> lts;
			if(optimizeStmts == OptimizeStmts.ON){
				lts = XstsLts.create(xsts,XstsStmtOptimizer.create(PredStmtOptimizer.getInstance()));
			} else {
				lts = XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
			}

			final Predicate<XstsState<PredState>> target = new XstsStatePredicate<ExprStatePredicate, PredState>(new ExprStatePredicate(negProp, abstractionSolver));
			final Analysis<XstsState<PredState>, XstsAction, PredPrec> analysis = XstsAnalysis.create(PredAnalysis.create(abstractionSolver, predAbstractor,
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
					exprTraceChecker = ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver());
					break;
				case BW_BIN_ITP:
					exprTraceChecker = ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver());
					break;
				case SEQ_ITP:
					exprTraceChecker = ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver());
					break;
				case MULTI_SEQ:
					exprTraceChecker = ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver());
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
		} else if (domain == Domain.EXPL_PRED_BOOL || domain == Domain.EXPL_PRED_CART || domain == Domain.EXPL_PRED_SPLIT || domain == Domain.EXPL_PRED_COMBINED) {
			final LTS<XstsState<Prod2State<ExplState,PredState>>, XstsAction> lts;
			if(optimizeStmts == OptimizeStmts.ON){
				lts = XstsLts.create(xsts,XstsStmtOptimizer.create(
						Prod2ExplPredStmtOptimizer.create(
								ExplStmtOptimizer.getInstance()
						)));
			} else {
				lts = XstsLts.create(xsts, XstsStmtOptimizer.create(DefaultStmtOptimizer.create()));
			}

			final Analysis<Prod2State<ExplState,PredState>,XstsAction,Prod2Prec<ExplPrec,PredPrec>> prod2Analysis;
			final Predicate<XstsState<Prod2State<ExplState, PredState>>> target = new XstsStatePredicate<ExprStatePredicate, Prod2State<ExplState, PredState>>(new ExprStatePredicate(negProp, abstractionSolver));
			if(domain == Domain.EXPL_PRED_BOOL || domain == Domain.EXPL_PRED_CART || domain == Domain.EXPL_PRED_SPLIT){
				final PredAbstractors.PredAbstractor predAbstractor;
				switch (domain) {
					case EXPL_PRED_BOOL:
						predAbstractor = PredAbstractors.booleanAbstractor(abstractionSolver);
						break;
					case EXPL_PRED_SPLIT:
						predAbstractor = PredAbstractors.booleanSplitAbstractor(abstractionSolver);
						break;
					case EXPL_PRED_CART:
						predAbstractor = PredAbstractors.cartesianAbstractor(abstractionSolver);
						break;
					default:
						throw new UnsupportedOperationException(domain + " domain is not supported.");
				}
				prod2Analysis = Prod2Analysis.create(
						ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), maxEnum),
						PredAnalysis.create(abstractionSolver, predAbstractor, xsts.getInitFormula()),
						Prod2ExplPredPreStrengtheningOperator.create(),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolver));
			} else {
				final Prod2ExplPredAbstractors.Prod2ExplPredAbstractor prodAbstractor = Prod2ExplPredAbstractors.booleanAbstractor(abstractionSolver);
				prod2Analysis = Prod2ExplPredAnalysis.create(
						ExplAnalysis.create(abstractionSolver, xsts.getInitFormula()),
						PredAnalysis.create(abstractionSolver, PredAbstractors.booleanAbstractor(abstractionSolver), xsts.getInitFormula()),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolver),
						prodAbstractor);
			}
			final Analysis<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> analysis = XstsAnalysis.create(prod2Analysis);

			final ArgBuilder<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> argBuilder = ArgBuilder.create(lts, analysis, target,
					true);
			final Abstractor<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> abstractor = BasicAbstractor.builder(argBuilder)
					.waitlist(PriorityWaitlist.create(search.comparator))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex())
					.logger(logger).build();

			Refiner<XstsState<Prod2State<ExplState, PredState>>, XstsAction, Prod2Prec<ExplPrec, PredPrec>> refiner = null;

			final Set<VarDecl<?>> ctrlVars = xsts.getCtrlVars();
			final RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> precRefiner = AutomaticItpRefToProd2ExplPredPrec.create(autoExpl.builder.create(xsts), predSplit.splitter);

			switch (refinement) {
				case FW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(precRefiner), pruneStrategy, logger);
					break;
				case BW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(precRefiner), pruneStrategy, logger);
					break;
				case SEQ_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(precRefiner), pruneStrategy, logger);
					break;
				case MULTI_SEQ:
					refiner = MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(xsts.getInitFormula(), negProp, solverFactory.createItpSolver()),
							JoiningPrecRefiner.create(precRefiner), pruneStrategy, logger);
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