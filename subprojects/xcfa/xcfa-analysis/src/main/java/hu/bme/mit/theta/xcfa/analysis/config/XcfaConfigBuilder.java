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
package hu.bme.mit.theta.xcfa.analysis.config;

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
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStmtAnalysis;
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec;
import hu.bme.mit.theta.analysis.expl.VarsRefToExplPrec;
import hu.bme.mit.theta.analysis.expr.BasicMultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.BasicStackableExprState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceNewtonChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUCBChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceUnsatCoreChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
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
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.DistToErrComparator;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaAnalysis;
import hu.bme.mit.theta.xcfa.analysis.XcfaInitPrecs;
import hu.bme.mit.theta.xcfa.analysis.XcfaLocationState;
import hu.bme.mit.theta.xcfa.analysis.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.lts.XcfaCachedLts;
import hu.bme.mit.theta.xcfa.analysis.lts.XcfaLts;
import hu.bme.mit.theta.xcfa.analysis.lts.XcfaSbeLts;
import hu.bme.mit.theta.xcfa.analysis.prec.GlobalXcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.prec.GlobalXcfaPrecRefiner;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XcfaConfigBuilder {
	public enum Domain {
		EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT
	}

	public enum Refinement {
		FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE, UCB,
		NWT_WP, NWT_SP, NWT_WP_LV, NWT_SP_LV, NWT_IT_WP, NWT_IT_SP, NWT_IT_WP_LV, NWT_IT_SP_LV
	}

	public enum Search {
		BFS {
			@Override
			public ArgNodeComparator getComp(final XCFA xcfa, final XcfaLocation errLoc) {
				return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs());
			}
		},

		DFS {
			@Override
			public ArgNodeComparator getComp(final XCFA xcfa, final XcfaLocation errLoc) {
				return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs());
			}
		},

		ERR {
			@Override
			public ArgNodeComparator getComp(final XCFA xcfa, final XcfaLocation errLoc) {
				return new DistToErrComparator(xcfa, errLoc);
			}
		};

		public abstract ArgNodeComparator getComp(XCFA xcfa, XcfaLocation errLoc);

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

	public enum PrecGranularity {
		GLOBAL {
			@Override
			public <P extends Prec> XcfaPrec<P> createPrec(final P innerPrec) {
				return GlobalXcfaPrec.create(innerPrec);
			}

			@Override
			public <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XcfaState<S, SS, SSS>, A, XcfaPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return GlobalXcfaPrecRefiner.create(refToPrec);
			}
		}/*,

		LOCAL {
			@Override
			public <P extends Prec> XcfaPrec<P> createPrec(final P innerPrec) {
				return LocalXcfaPrec.create(innerPrec);
			}

			@Override
			public <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XcfaState<S, SS, SSS>, A, XcfaPrec<P>, R> createRefiner(
					final RefutationToPrec<P, R> refToPrec) {
				return LocalXcfaPrecRefiner.create(refToPrec);
			}
		}*/;

		public abstract <P extends Prec> XcfaPrec<P> createPrec(P innerPrec);

		public abstract <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XcfaState<S, SS, SSS>, A, XcfaPrec<P>, R> createRefiner(
				RefutationToPrec<P, R> refToPrec);
	}

	public enum Encoding {
		SBE {
			@Override
			public XcfaLts getLts(XcfaLocation errorLoc) {
				return new XcfaCachedLts(XcfaSbeLts.getInstance());
			}
		}/*,

		LBE {
			@Override
			public XcfaLts getLts(XcfaLocation errorLoc) {
				return new XcfaCachedLts(XcfaLbeLts.of(errorLoc));
			}
		}*/;

		public abstract XcfaLts getLts(XcfaLocation errorLoc);
	}

	public enum InitPrec {
		EMPTY, ALLVARS, ALLASSUMES
	}

	private Logger logger = NullLogger.getInstance();
	private final SolverFactory solverFactory;
	private final Domain domain;
	private final Refinement refinement;
	private Search search = Search.BFS;
	private PredSplit predSplit = PredSplit.WHOLE;
	private PrecGranularity precGranularity = PrecGranularity.GLOBAL;
	private Encoding encoding = Encoding.SBE;
	private int maxEnum = 0;
	private InitPrec initPrec = InitPrec.EMPTY;
	private PruneStrategy pruneStrategy = PruneStrategy.LAZY;

	public XcfaConfigBuilder(final Domain domain, final Refinement refinement, final SolverFactory solverFactory) {
		this.domain = domain;
		this.refinement = refinement;
		this.solverFactory = solverFactory;
	}

	public XcfaConfigBuilder logger(final Logger logger) {
		this.logger = logger;
		return this;
	}

	public XcfaConfigBuilder search(final Search search) {
		this.search = search;
		return this;
	}

	public XcfaConfigBuilder predSplit(final PredSplit predSplit) {
		this.predSplit = predSplit;
		return this;
	}

	public XcfaConfigBuilder precGranularity(final PrecGranularity precGranularity) {
		this.precGranularity = precGranularity;
		return this;
	}

	public XcfaConfigBuilder encoding(final Encoding encoding) {
		this.encoding = encoding;
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

	public XcfaConfig<? extends State, ? extends Action, ? extends Prec> build(final XCFA xcfa, final XcfaLocation errLoc) {
		final ItpSolver solver = solverFactory.createItpSolver();
		final XcfaLts lts = encoding.getLts(errLoc);

		if (domain == Domain.EXPL) {
			final Analysis<XcfaState<ExplState, BasicStackableExprState<XcfaLocationState<ExplState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<ExplState>, BasicStackableExprState<XcfaLocationState<ExplState>>>>, XcfaAction, XcfaPrec<ExplPrec>> analysis = XcfaAnalysis
					.create(xcfa.getProcesses().stream().map(process -> Map.entry(process.hashCode(), process.getMainProcedure().getInitLoc())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)), ExplStmtAnalysis.create(solver, True(), maxEnum));
			final ArgBuilder<XcfaState<ExplState, BasicStackableExprState<XcfaLocationState<ExplState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<ExplState>, BasicStackableExprState<XcfaLocationState<ExplState>>>>, XcfaAction, XcfaPrec<ExplPrec>> argBuilder = ArgBuilder.create(lts,
					analysis, XcfaState::isErrorState, true);
			final Abstractor<XcfaState<ExplState, BasicStackableExprState<XcfaLocationState<ExplState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<ExplState>, BasicStackableExprState<XcfaLocationState<ExplState>>>>, XcfaAction, XcfaPrec<ExplPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(XcfaState::getLocations)
					.waitlist(PriorityWaitlist.create(search.getComp(xcfa, errLoc)))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex()).logger(logger).build();

			Refiner<XcfaState<ExplState, BasicStackableExprState<XcfaLocationState<ExplState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<ExplState>, BasicStackableExprState<XcfaLocationState<ExplState>>>>, XcfaAction, XcfaPrec<ExplPrec>> refiner;

			switch (refinement) {
				case FW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case BW_BIN_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case SEQ_ITP:
					refiner = SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case MULTI_SEQ:
					refiner = MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case UNSAT_CORE:
					refiner = SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new VarsRefToExplPrec()), pruneStrategy, logger);
					break;
				case UCB:
					refiner = SingleExprTraceRefiner.create(ExprTraceUCBChecker.create(True(), True(), solver),
							precGranularity.createRefiner(new ItpRefToExplPrec()), pruneStrategy, logger);
					break;
				case NWT_SP:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withSP().withoutLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_WP:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withWP().withoutLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_SP_LV:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withSP().withLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_WP_LV:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withWP().withLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_IT_SP:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withSP().withoutLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_IT_WP:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withWP().withoutLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_IT_SP_LV:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withSP().withLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				case NWT_IT_WP_LV:
					refiner = SingleExprTraceRefiner.create(
						ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withWP().withLV(),
						precGranularity.createRefiner(new ItpRefToExplPrec()),
						pruneStrategy,
						logger
					);
					break;
				default:
					throw new UnsupportedOperationException(
							domain + " domain does not support " + refinement + " refinement.");
			}

			final SafetyChecker<XcfaState<ExplState, BasicStackableExprState<XcfaLocationState<ExplState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<ExplState>, BasicStackableExprState<XcfaLocationState<ExplState>>>>, XcfaAction, XcfaPrec<ExplPrec>> checker = CegarChecker
					.create(abstractor, refiner, logger);

			XcfaPrec<ExplPrec> prec;

			switch (initPrec){
				case EMPTY:
					prec = precGranularity.createPrec(ExplPrec.empty());
					break;
				case ALLVARS:
					prec = precGranularity.createPrec(ExplPrec.of(XcfaUtils.getVars(xcfa)));
					break;
				default:
					throw new UnsupportedOperationException(initPrec + " initial precision is not supported with " +
							domain + " domain");
			}

			return XcfaConfig.create(checker, prec);

		} else if (domain == Domain.PRED_BOOL || domain == Domain.PRED_CART || domain == Domain.PRED_SPLIT) {
			PredAbstractor predAbstractor;
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
			final Analysis<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> analysis = XcfaAnalysis
					.create(xcfa.getProcesses().stream().map(process -> Map.entry(process.hashCode(), process.getMainProcedure().getInitLoc())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)), PredAnalysis.create(solver, predAbstractor, True()));
			final ArgBuilder<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> argBuilder = ArgBuilder.create(lts,
					analysis, XcfaState::isErrorState, true);
			final Abstractor<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> abstractor = BasicAbstractor
					.builder(argBuilder).projection(XcfaState::getLocations)
					.waitlist(PriorityWaitlist.create(search.getComp(xcfa, errLoc)))
					.stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration()
							: StopCriterions.firstCex()).logger(logger).build();

			ExprTraceChecker<ItpRefutation> exprTraceChecker;
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
				case MULTI_SEQ:
					exprTraceChecker = ExprTraceSeqItpChecker.create(True(), True(), solver);
					break;
				case UCB:
					exprTraceChecker = ExprTraceUCBChecker.create(True(), True(), solver);
					break;
				case NWT_SP:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withSP().withoutLV();
					break;
				case NWT_WP:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withWP().withoutLV();
					break;
				case NWT_SP_LV:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withSP().withLV();
					break;
				case NWT_WP_LV:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withoutIT().withWP().withLV();
					break;
				case NWT_IT_SP:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withSP().withoutLV();
					break;
				case NWT_IT_WP:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withWP().withoutLV();
					break;
				case NWT_IT_SP_LV:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withSP().withLV();
					break;
				case NWT_IT_WP_LV:
					exprTraceChecker = ExprTraceNewtonChecker.create(True(), True(), solver).withIT().withWP().withLV();
					break;
				default:
					throw new UnsupportedOperationException(
							domain + " domain does not support " + refinement + " refinement.");
			}
			final ItpRefToPredPrec refToPrec = new ItpRefToPredPrec(predSplit.splitter);
			Refiner<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> refiner;

			if (refinement == Refinement.MULTI_SEQ) {
				refiner = MultiExprTraceRefiner.create(exprTraceChecker,
						precGranularity.createRefiner(refToPrec), pruneStrategy, logger);
			} else {
				refiner = SingleExprTraceRefiner.create(exprTraceChecker,
						precGranularity.createRefiner(refToPrec), pruneStrategy, logger);
			}

			final SafetyChecker<XcfaState<PredState, BasicStackableExprState<XcfaLocationState<PredState>>, BasicMultiStackableExprState<Integer, XcfaLocationState<PredState>, BasicStackableExprState<XcfaLocationState<PredState>>>>, XcfaAction, XcfaPrec<PredPrec>> checker = CegarChecker
					.create(abstractor, refiner, logger);

			XcfaPrec<PredPrec> prec;

			switch (initPrec){
				case EMPTY:
					prec = precGranularity.createPrec(PredPrec.of());
					break;
				case ALLASSUMES:
					switch (precGranularity){
						/*case LOCAL:
							prec = XcfaInitPrecs.collectAssumesLocal(xcfa);
							break;*/
						case GLOBAL:
							prec = XcfaInitPrecs.collectAssumesGlobal(xcfa);
							break;
						default:
							throw new UnsupportedOperationException(precGranularity +
									" precision granularity is not supported with " + domain + " domain");
					}
					break;
				default:
					throw new UnsupportedOperationException(initPrec + " initial precision is not supported with " +
							domain + " domain");
			}

			return XcfaConfig.create(checker, prec);

		} else {
			throw new UnsupportedOperationException(domain + " domain is not supported.");
		}
	}
}
