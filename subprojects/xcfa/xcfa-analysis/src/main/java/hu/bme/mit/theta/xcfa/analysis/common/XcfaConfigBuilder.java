/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis.common;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplStmtAnalysis;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceNewtonChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUCBChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.MultiExprTraceRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.PruneStrategy;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.analysis.expr.refinement.SingleExprTraceRefiner;
import hu.bme.mit.theta.analysis.pred.ExprSplitters;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.ItpRefToPredPrec;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.analysis.pred.PredAnalysis;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.AutomaticItpRefToProd2ExplPredPrec;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredAbstractors;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredStmtAnalysis;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.Prod2ExplPredStrengtheningOperator;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.common.autoexpl.XcfaAutoExpl;
import hu.bme.mit.theta.xcfa.analysis.common.autoexpl.XcfaGlobalStaticAutoExpl;
import hu.bme.mit.theta.xcfa.analysis.common.autoexpl.XcfaNewAtomsAutoExpl;
import hu.bme.mit.theta.xcfa.analysis.common.autoexpl.XcfaNewOperandsAutoExpl;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaInitFunc;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaLts;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaOrd;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaPrecRefiner;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaTransFunc;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaDistToErrComparator;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTInitFunc;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTLts;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTOrd;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTPrecRefiner;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.XcfaSTTransFunc;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

@SuppressWarnings({"rawtypes", "unchecked"})
public class XcfaConfigBuilder {
	public enum Domain {
		EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT, EXPL_PRED_COMBINED;
	}

	public enum Refinement {
		FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE, UCB,
		NWT_WP, NWT_SP, NWT_WP_LV, NWT_SP_LV, NWT_IT_WP, NWT_IT_SP, NWT_IT_WP_LV, NWT_IT_SP_LV
	}

	public enum Algorithm {
		SINGLETHREAD{
			@Override
			public LTS<? extends XcfaState<?>, ? extends XcfaAction> getLts() {
				return new XcfaSTLts();
			}

			@Override
			public <S extends ExprState, P extends Prec> InitFunc<XcfaState<S>, XcfaPrec<P>> getInitFunc(final List<XcfaLocation> initLocs, final InitFunc<S, P> initFunc) {
				checkArgument(initLocs.size() == 1, "Single threaded algorithm can only handle single-init-location programs!");
				return XcfaSTInitFunc.create(initLocs.get(0), initFunc);
			}

			@Override
			public <S extends ExprState, A extends StmtAction, P extends Prec> TransFunc<XcfaState<S>, A, XcfaPrec<P>> getTransFunc(final TransFunc<S, A, P> transFunc) {
				return XcfaSTTransFunc.create(transFunc);
			}

			@Override
			public <P extends Prec, R extends Refutation> PrecRefiner<XcfaState<ExprState>, ? extends StmtAction, XcfaPrec<P>, R> getPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
				return XcfaSTPrecRefiner.create(refToPrec);
			}

			@Override
			public <S extends ExprState> PartialOrd<XcfaState<S>> getPartialOrder(final PartialOrd<S> partialOrd) {
				return XcfaSTOrd.create(partialOrd);
			}

			@Override
			public <S extends ExprState, P extends Prec, A extends StmtAction> Analysis<XcfaState<S>, A, XcfaPrec<P>> getAnalysis(final List<XcfaLocation> initLocs, final Analysis<S, A, P> analysis) {
				return XcfaAnalysis.create(initLocs, getPartialOrder(analysis.getPartialOrd()), getInitFunc(initLocs, analysis.getInitFunc()), getTransFunc(analysis.getTransFunc()));
			}
		},

		INTERLEAVINGS{
			@Override
			public LTS<? extends XcfaState<?>, ? extends XcfaAction> getLts() {
				return new XcfaLts();
			}

			@Override
			public <S extends ExprState, P extends Prec> InitFunc<XcfaState<S>, XcfaPrec<P>> getInitFunc(final List<XcfaLocation> initLocs, final InitFunc<S, P> initFunc) {
				return XcfaInitFunc.create(initLocs, initFunc);
			}

			@Override
			public <S extends ExprState, A extends StmtAction, P extends Prec> TransFunc<XcfaState<S>, A, XcfaPrec<P>> getTransFunc(final TransFunc<S, A, P> transFunc) {
				return XcfaTransFunc.create(transFunc);
			}

			@Override
			public <P extends Prec, R extends Refutation> PrecRefiner<XcfaState<ExprState>, ? extends StmtAction, XcfaPrec<P>, R> getPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
				return XcfaPrecRefiner.create(refToPrec);
			}

			@Override
			public <S extends ExprState> PartialOrd<XcfaState<S>> getPartialOrder(final PartialOrd<S> partialOrd) {
				return XcfaOrd.create(partialOrd);
			}

			@Override
			public <S extends ExprState, P extends Prec, A extends StmtAction> Analysis<XcfaState<S>, A, XcfaPrec<P>> getAnalysis(final List<XcfaLocation> initLocs, final Analysis<S, A, P> analysis) {
				return XcfaAnalysis.create(initLocs, getPartialOrder(analysis.getPartialOrd()), getInitFunc(initLocs, analysis.getInitFunc()), getTransFunc(analysis.getTransFunc()));
			}
		};

		public abstract LTS<? extends XcfaState<?>, ? extends XcfaAction> getLts();
		public abstract <S extends ExprState, P extends Prec> InitFunc<XcfaState<S>, XcfaPrec<P>> getInitFunc(final List<XcfaLocation> initLocs, final InitFunc<S, P> initFunc);
		public abstract <S extends ExprState, A extends StmtAction, P extends Prec> TransFunc<XcfaState<S>, A, XcfaPrec<P>>  getTransFunc(final TransFunc<S, A, P> transFunc);
		public abstract  <P extends Prec, R extends Refutation> PrecRefiner<XcfaState<ExprState>, ? extends StmtAction, XcfaPrec<P>, R> getPrecRefiner(final RefutationToPrec<P, R> refToPrec);
		public abstract <S extends ExprState> PartialOrd<XcfaState<S>> getPartialOrder(final PartialOrd<S> partialOrd);
		public abstract  <S extends ExprState, P extends Prec, A extends StmtAction> Analysis<? extends XcfaState<? extends S>,  ? extends A, ? extends XcfaPrec<P>> getAnalysis(final List<XcfaLocation> initLoc, final Analysis<S, A, P> analysis);
		}

	public enum Search {
		BFS {
			@Override
			public ArgNodeComparator getComp(final XCFA cfa, final XcfaLocation errLoc) {
				return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs());
			}
		},

		DFS {
			@Override
			public ArgNodeComparator getComp(final XCFA cfa, final XcfaLocation errLoc) {
				return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs());
			}
		},

		ERR {
			@Override
			public ArgNodeComparator getComp(final XCFA cfa, final XcfaLocation errLoc) {
				return new XcfaDistToErrComparator(cfa, errLoc);
			}
		};

		public abstract ArgNodeComparator getComp(final XCFA cfa, final XcfaLocation errLoc);

	}

	public enum PredSplit {
		WHOLE(ExprSplitters.whole()),

		CONJUNCTS(ExprSplitters.conjuncts()),

		ATOMS(ExprSplitters.atoms());

		public final ExprSplitter splitter;

		PredSplit(final ExprSplitter splitter) {
			this.splitter = splitter;
		}
	}

	public enum InitPrec {
		EMPTY, ALLVARS, ALLGLOBALS, EVERYTHING, ALLASSUMES
	}

	public enum AutoExpl {
		STATIC(new XcfaGlobalStaticAutoExpl()),

		NEWATOMS(new XcfaNewAtomsAutoExpl()),

		NEWOPERANDS(new XcfaNewOperandsAutoExpl());

		public final XcfaAutoExpl builder;

		private AutoExpl(final XcfaAutoExpl builder) { this.builder = builder; }
	}

	private Logger logger = NullLogger.getInstance();
	private final SolverFactory refinementSolverFactory;
	private final SolverFactory abstractionSolverFactory;
	private final Domain domain;
	private final Refinement refinement;
	private final Algorithm algorithm;
	private boolean preCheck = true;
	private Search search = Search.BFS;
	private PredSplit predSplit = PredSplit.WHOLE;
	private int maxEnum = 0;
	private InitPrec initPrec = InitPrec.EMPTY;
	private PruneStrategy pruneStrategy = PruneStrategy.LAZY;
	private AutoExpl autoExpl = AutoExpl.NEWOPERANDS;

	public XcfaConfigBuilder(final Domain domain, final Refinement refinement, final SolverFactory refinementSolverFactory, final SolverFactory abstractionSolverFactory, final Algorithm algorithm) {
		this.domain = domain;
		this.refinement = refinement;
		this.refinementSolverFactory = refinementSolverFactory;
		this.abstractionSolverFactory = abstractionSolverFactory;
		this.algorithm = algorithm;
	}

	public XcfaConfigBuilder autoExpl(final AutoExpl autoExpl) {
		this.autoExpl = autoExpl;
		return this;
	}

	public XcfaConfigBuilder preCheck(final boolean preCheck) {
		this.preCheck = preCheck;
		return this;
	}

	public XcfaConfigBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public XcfaConfigBuilder search(final Search search) {
		checkArgument(!(search == Search.ERR) || algorithm == Algorithm.SINGLETHREAD, "ERR search only compatible with SINGLETHREAD algorithm!");
		this.search = search;
		return this;
	}

	public XcfaConfigBuilder predSplit(final PredSplit predSplit) {
		this.predSplit = predSplit;
		return this;
	}

	public XcfaConfigBuilder maxEnum(final int maxEnum) {
		this.maxEnum = maxEnum;
		return this;
	}

	public XcfaConfigBuilder initPrec(final InitPrec initPrec) {
		this.initPrec = initPrec;
		return this;
	}

	public XcfaConfigBuilder pruneStrategy(final PruneStrategy pruneStrategy) {
		this.pruneStrategy = pruneStrategy;
		return this;
	}

	public XcfaConfig<? extends State, ? extends Action, ? extends Prec> build(final XCFA xcfa) {
		final LTS lts = algorithm.getLts();
		final Abstractor abstractor;
		final Refiner refiner;
		final XcfaPrec prec;
		final PrecRefiner precRefiner;

		final ItpRefToPredPrec predRefToPrec = new ItpRefToPredPrec(predSplit.splitter);
		final ItpRefToExplPrec explRefToPrec = new ItpRefToExplPrec();

		switch(domain){
			case EXPL:
				final ExplStmtAnalysis domainAnalysis = ExplStmtAnalysis.create(abstractionSolverFactory.createSolver(), True(), maxEnum);
				abstractor = getAbstractor(lts, domainAnalysis, xcfa);
				prec = getExplPrec(initPrec, xcfa);
				precRefiner = algorithm.getPrecRefiner(explRefToPrec);
				break;
			case PRED_BOOL:
				PredAbstractor predAbstractor = PredAbstractors.booleanAbstractor(abstractionSolverFactory.createSolver());
				PredAnalysis<?> predAnalysis = PredAnalysis.create(abstractionSolverFactory.createSolver(), predAbstractor, True());
				abstractor = getAbstractor(lts, predAnalysis, xcfa);
				prec = getPredPrec(initPrec, xcfa);
				precRefiner = algorithm.getPrecRefiner(predRefToPrec);
				break;
			case PRED_CART:
				predAbstractor = PredAbstractors.booleanSplitAbstractor(abstractionSolverFactory.createSolver());
				predAnalysis = PredAnalysis.create(abstractionSolverFactory.createSolver(), predAbstractor, True());
				abstractor = getAbstractor(lts, predAnalysis, xcfa);
				prec = getPredPrec(initPrec, xcfa);
				precRefiner = algorithm.getPrecRefiner(predRefToPrec);
				break;
			case PRED_SPLIT:
				predAbstractor = PredAbstractors.cartesianAbstractor(abstractionSolverFactory.createSolver());
				predAnalysis = PredAnalysis.create(abstractionSolverFactory.createSolver(), predAbstractor, True());
				abstractor = getAbstractor(lts, predAnalysis, xcfa);
				prec = getPredPrec(initPrec, xcfa);
				precRefiner = algorithm.getPrecRefiner(predRefToPrec);
				break;
			case EXPL_PRED_COMBINED:
				final Prod2ExplPredAbstractors.Prod2ExplPredAbstractor prodAbstractor = Prod2ExplPredAbstractors.booleanAbstractor(abstractionSolverFactory.createSolver());
				final Prod2ExplPredStmtAnalysis prodAnalysis = Prod2ExplPredStmtAnalysis.create(
						ExplStmtAnalysis.create(abstractionSolverFactory.createSolver(), True()),
						PredAnalysis.create(abstractionSolverFactory.createSolver(), PredAbstractors.booleanAbstractor(abstractionSolverFactory.createSolver()), True()),
						Prod2ExplPredStrengtheningOperator.create(abstractionSolverFactory.createSolver()),
						prodAbstractor, abstractionSolverFactory.createSolver(), maxEnum);
				abstractor = getAbstractor(lts, prodAnalysis, xcfa);
				prec = getProdPrec(initPrec, xcfa);
				precRefiner = algorithm.getPrecRefiner(AutomaticItpRefToProd2ExplPredPrec.create(autoExpl.builder.create(xcfa), predSplit.splitter));
				break;
			default:
				throw new IllegalStateException("Unexpected value: " + domain);
		}

		final ExprTraceChecker exprTraceChecker;

		switch (refinement) {
			case FW_BIN_ITP:
				exprTraceChecker = ExprTraceFwBinItpChecker.create(True(), True(), refinementSolverFactory.createItpSolver());
				break;
			case BW_BIN_ITP:
				exprTraceChecker = ExprTraceBwBinItpChecker.create(True(), True(), refinementSolverFactory.createItpSolver());
				break;
			case SEQ_ITP:
				exprTraceChecker = ExprTraceSeqItpChecker.create(True(), True(), refinementSolverFactory.createItpSolver());
				break;
			case MULTI_SEQ:
				exprTraceChecker = ExprTraceSeqItpChecker.create(True(), True(), refinementSolverFactory.createItpSolver());
				break;
			case UCB:
				exprTraceChecker = ExprTraceUCBChecker.create(True(), True(), refinementSolverFactory.createUCSolver());
				break;
			case UNSAT_CORE:
				exprTraceChecker = ExprTraceUnsatCoreChecker.create(True(), True(), refinementSolverFactory.createUCSolver());
				break;
			case NWT_SP:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withoutIT().withSP().withoutLV();
				break;
			case NWT_WP:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withoutIT().withWP().withoutLV();
				break;
			case NWT_SP_LV:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withoutIT().withSP().withLV();
				break;
			case NWT_WP_LV:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withoutIT().withWP().withLV();
				break;
			case NWT_IT_SP:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withIT().withSP().withoutLV();
				break;
			case NWT_IT_WP:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withIT().withWP().withoutLV();
				break;
			case NWT_IT_SP_LV:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withIT().withSP().withLV();
				break;
			case NWT_IT_WP_LV:
				exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), refinementSolverFactory.createUCSolver()).withIT().withWP().withLV();
				break;
			default:
				throw new UnsupportedOperationException(
						domain + " domain does not support " + refinement + " refinement.");
		}

		if (refinement == Refinement.MULTI_SEQ) {
			refiner = MultiExprTraceRefiner.create(exprTraceChecker,
					precRefiner, pruneStrategy, logger);
		} else {
			refiner = SingleExprTraceRefiner.create(exprTraceChecker,
					precRefiner, pruneStrategy, logger);
		}
		final SafetyChecker checker = CegarChecker.create(abstractor, refiner, logger);
		return XcfaConfig.create(checker, prec);
	}

	private XcfaPrec getProdPrec(InitPrec initPrec, XCFA xcfa) {
		ExplPrec explPrec = ExplPrec.empty();
		PredPrec predPrec = PredPrec.of();

		switch (initPrec){
			case EMPTY:
				break;
			case ALLASSUMES:
				predPrec = XcfaPrec.collectAssumes(xcfa).getGlobalPrec();
				break;
			case ALLVARS:
				explPrec = ExplPrec.of(XcfaUtils.getVars(xcfa));
				break;
			case ALLGLOBALS:
				explPrec = ExplPrec.of(xcfa.getGlobalVars());
				break;
			case EVERYTHING:
				predPrec = XcfaPrec.collectAssumes(xcfa).getGlobalPrec();
				explPrec = ExplPrec.of(XcfaUtils.getVars(xcfa));
				break;
			default:
				throw new UnsupportedOperationException(initPrec + " initial precision is not supported with " +
						domain + " domain");
		}
		return XcfaPrec.create(Prod2Prec.of(explPrec, predPrec));
	}

	private XcfaPrec getExplPrec(InitPrec initPrec, XCFA xcfa) {
		switch (initPrec){
			case EMPTY:
				return XcfaPrec.create(ExplPrec.empty());
			case ALLVARS:
				return XcfaPrec.create(ExplPrec.of(XcfaUtils.getVars(xcfa)));
			case ALLGLOBALS:
				return XcfaPrec.create(ExplPrec.of(xcfa.getGlobalVars()));
			default:
				throw new UnsupportedOperationException(initPrec + " initial precision is not supported with " +
						domain + " domain");
		}
	}
	private XcfaPrec getPredPrec(InitPrec initPrec, XCFA xcfa) {
		switch (initPrec){
			case EMPTY:
				return XcfaPrec.create(PredPrec.of());
			case ALLASSUMES:
				return XcfaPrec.collectAssumes(xcfa);
			default:
				throw new UnsupportedOperationException(initPrec + " initial precision is not supported with " +
						domain + " domain");
		}
	}

	private	Abstractor getAbstractor(LTS lts, Analysis domainAnalysis, XCFA xcfa) {
		final Analysis analysis = algorithm.getAnalysis(xcfa.getProcesses().stream().map(proc -> proc.getMainProcedure().getInitLoc()).collect(Collectors.toList()), domainAnalysis);

		final ArgBuilder argBuilder = ArgBuilder.create(lts, analysis, state -> ((XcfaState)state).isError(), true);
		return BasicAbstractor
				.builder(argBuilder).projection(state -> ((XcfaState)state).getCurrentLoc())
				.waitlist(PriorityWaitlist.create(search.getComp(xcfa, xcfa.getMainProcess().getMainProcedure().getErrorLoc())))
				.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
						: StopCriterions.firstCex()).logger(logger).build();
	}
}
