/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.cfa.analysis.config;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators.ArgNodeComparator;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter;
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.unit.UnitState;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.*;
import hu.bme.mit.theta.cfa.analysis.lts.CfaCachedLts;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLbeLts;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts;
import hu.bme.mit.theta.cfa.analysis.lts.CfaSbeLts;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec;
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrecRefiner;
import hu.bme.mit.theta.cfa.analysis.prec.LocalCfaPrec;
import hu.bme.mit.theta.cfa.analysis.prec.LocalCfaPrecRefiner;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class CfaConfigBuilder {

    private final SolverFactory abstractionSolverFactory;
    private final SolverFactory refinementSolverFactory;
    private final Domain domain;
    private final Refinement refinement;
    private Logger logger = NullLogger.getInstance();
    private Search search = Search.BFS;
    private PredSplit predSplit = PredSplit.WHOLE;
    private PrecGranularity precGranularity = PrecGranularity.GLOBAL;
    private Encoding encoding = Encoding.LBE;
    private int maxEnum = 0;
    private InitPrec initPrec = InitPrec.EMPTY;
    private PruneStrategy pruneStrategy = PruneStrategy.LAZY;

    public CfaConfigBuilder(final Domain domain, final Refinement refinement,
                            final SolverFactory solverFactory) {
        this.domain = domain;
        this.refinement = refinement;
        this.abstractionSolverFactory = solverFactory;
        this.refinementSolverFactory = solverFactory;
    }

    public CfaConfigBuilder(final Domain domain, final Refinement refinement,
                            final SolverFactory abstractionSolverFactory, final SolverFactory refinementSolverFactory) {
        this.domain = domain;
        this.refinement = refinement;
        this.abstractionSolverFactory = abstractionSolverFactory;
        this.refinementSolverFactory = refinementSolverFactory;
    }

    public CfaConfigBuilder logger(final Logger logger) {
        this.logger = logger;
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

    public CfaConfigBuilder encoding(final Encoding encoding) {
        this.encoding = encoding;
        return this;
    }

    public CfaConfigBuilder maxEnum(final int maxEnum) {
        this.maxEnum = maxEnum;
        return this;
    }

    public CfaConfigBuilder initPrec(final InitPrec initPrec) {
        this.initPrec = initPrec;
        return this;
    }

    public CfaConfigBuilder pruneStrategy(final PruneStrategy pruneStrategy) {
        this.pruneStrategy = pruneStrategy;
        return this;
    }

    public CfaConfig<? extends State, ? extends Action, ? extends Prec> build(final CFA cfa,
                                                                              final CFA.Loc errLoc) {
        if (domain == Domain.EXPL) {
            return (new ExplStrategy(cfa)).buildConfig(errLoc);
        }
        if (domain == Domain.PRED_BOOL || domain == Domain.PRED_CART
                || domain == Domain.PRED_SPLIT) {
            return (new PredStrategy(cfa)).buildConfig(errLoc);
        }
        throw new UnsupportedOperationException(domain + " domain is not supported.");
    }

    public enum Algorithm {
        CEGAR,
        BMC,
        KINDUCTION,
        IMC
    }

    public enum Domain {
        EXPL(null),
        PRED_BOOL(PredAbstractors::booleanAbstractor),
        PRED_CART(PredAbstractors::cartesianAbstractor),
        PRED_SPLIT(PredAbstractors::booleanSplitAbstractor);

        public final Function<Solver, PredAbstractor> predAbstractorFunction;

        Domain(final Function<Solver, PredAbstractor> predAbstractorFunction) {
            this.predAbstractorFunction = predAbstractorFunction;
        }
    }

    public enum Refinement {
        FW_BIN_ITP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceFwBinItpChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createItpSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, BW_BIN_ITP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceBwBinItpChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createItpSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, SEQ_ITP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createItpSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        },
        MULTI_SEQ {
            @Override
            public <S extends ExprState> StopCriterion<S, CfaAction> getStopCriterion() {
                return StopCriterions.fullExploration();
            }

            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return MultiExprTraceRefiner.create(ExprTraceSeqItpChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createItpSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        },
        UNSAT_CORE {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceUnsatCoreChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getVarsRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, UCB {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceUCBChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        },
        NWT_WP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withoutIT().withSP().withoutLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_SP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withoutIT().withWP().withoutLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_WP_LV {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withoutIT().withWP().withLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_SP_LV {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withoutIT().withSP().withLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_IT_WP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withIT().withWP().withoutLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_IT_SP {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withIT().withSP().withoutLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_IT_WP_LV {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withIT().withWP().withLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        }, NWT_IT_SP_LV {
            @Override
            public <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy) {
                return SingleExprTraceRefiner.create(ExprTraceNewtonChecker.create(True(), True(), builderStrategy.getRefinementSolverFactory().createUCSolver()).withIT().withSP().withLV(), builderStrategy.getPrecGranularity().createRefiner(builderStrategy.getItpRefToPrec()), builderStrategy.getPruneStrategy(), builderStrategy.getLogger());
            }
        };

        public <S extends ExprState> StopCriterion<S, CfaAction> getStopCriterion() {
            return StopCriterions.firstCex();
        }

        public abstract <S extends ExprState, P extends Prec> ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> getRefiner(BuilderStrategy<S, P> builderStrategy);

    }

    public enum Search {
        BFS {
            @Override
            public ArgNodeComparator getComp(final CFA cfa, final CFA.Loc errLoc) {
                return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(),
                        ArgNodeComparators.bfs());
            }
        },

        DFS {
            @Override
            public ArgNodeComparator getComp(final CFA cfa, final CFA.Loc errLoc) {
                return ArgNodeComparators.combine(ArgNodeComparators.targetFirst(),
                        ArgNodeComparators.dfs());
            }
        },

        ERR {
            @Override
            public ArgNodeComparator getComp(final CFA cfa, final CFA.Loc errLoc) {
                return new DistToErrComparator(cfa, errLoc);
            }
        };

        public abstract ArgNodeComparator getComp(CFA cfa, CFA.Loc errLoc);

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
            public <P extends Prec> CfaPrec<P> createPrec(final P innerPrec) {
                return GlobalCfaPrec.create(innerPrec);
            }

            @Override
            public <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> createRefiner(
                    final RefutationToPrec<P, R> refToPrec) {
                return GlobalCfaPrecRefiner.create(refToPrec);
            }

            @Override
            public CfaPrec<PredPrec> assumePrecs(CFA cfa) {
                return CfaInitPrecs.collectAssumesGlobal(cfa);
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

            @Override
            public CfaPrec<PredPrec> assumePrecs(CFA cfa) {
                return CfaInitPrecs.collectAssumesLocal(cfa);
            }
        };

        public abstract <P extends Prec> CfaPrec<P> createPrec(P innerPrec);

        public abstract <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> createRefiner(
                RefutationToPrec<P, R> refToPrec);

        public abstract CfaPrec<PredPrec> assumePrecs(CFA cfa);
    }

    public enum Encoding {
        SBE {
            @Override
            public CfaLts getLts(CFA.Loc errorLoc) {
                return new CfaCachedLts(CfaSbeLts.getInstance());
            }
        },

        LBE {
            @Override
            public CfaLts getLts(CFA.Loc errorLoc) {
                return new CfaCachedLts(CfaLbeLts.of(errorLoc));
            }
        };

        public abstract CfaLts getLts(CFA.Loc errorLoc);
    }

    public enum InitPrec {
        EMPTY, ALLVARS, ALLASSUMES
    }

    public abstract class BuilderStrategy<S extends ExprState, P extends Prec> {

        protected static final String UNSUPPORTED_CONFIG_VALUE = "Builder strategy %s does not support configuration value %s as %s";
        protected final CFA cfa;

        @SuppressWarnings("java:S1699")
        protected BuilderStrategy(CFA cfa) {
            checkState(getSupportedDomains().contains(domain), UNSUPPORTED_CONFIG_VALUE, getClass().getSimpleName(), domain, "domain");
            checkState(getSupportedRefinements().contains(refinement), UNSUPPORTED_CONFIG_VALUE, getClass().getSimpleName(), refinement, "refinement");
            checkState(getSupportedInitPrecs().contains(initPrec), UNSUPPORTED_CONFIG_VALUE, getClass().getSimpleName(), initPrec, "initial precision");
            this.cfa = cfa;
        }

        public abstract Set<Domain> getSupportedDomains();

        public abstract Set<Refinement> getSupportedRefinements();

        public abstract Set<InitPrec> getSupportedInitPrecs();

        public abstract Analysis<S, StmtAction, ? super P> getDataAnalysis();

        public CfaAnalysis<S, P> getAnalysis() {
            return CfaAnalysis.create(cfa.getInitLoc(), getDataAnalysis());
        }

        public abstract RefutationToPrec<P, ItpRefutation> getItpRefToPrec();

        public RefutationToPrec<P, VarsRefutation> getVarsRefToPrec() {
            throw new UnsupportedOperationException(String.format("Builder strategy %s can not provide Vars refutation to precision", getClass().getSimpleName()));
        }

        protected SolverFactory getRefinementSolverFactory() {
            return refinementSolverFactory;
        }

        protected PrecGranularity getPrecGranularity() {
            return precGranularity;
        }

        protected PruneStrategy getPruneStrategy() {
            return pruneStrategy;
        }

        protected Logger getLogger() {
            return logger;
        }

        public abstract CfaPrec<P> createInitPrec();

        public CfaLts getLts(CFA.Loc errLoc) {
            return encoding.getLts(errLoc);
        }

        public CfaLts getLts() {
            return getLts(cfa.getErrorLoc().orElse(CFA.builder().createLoc()));
        }

        public CfaConfig<CfaState<S>, CfaAction, CfaPrec<P>> buildConfig(CFA.Loc errLoc) {
            final Predicate<CfaState<S>> target = new CfaErrorlocPredicate<>(errLoc);
            final Analysis<CfaState<S>, CfaAction, CfaPrec<P>> analysis = getAnalysis();
            final ArgBuilder<CfaState<S>, CfaAction, CfaPrec<P>> argBuilder = ArgBuilder.create(
                    getLts(errLoc), analysis, target,
                    true);
            final ArgAbstractor<CfaState<S>, CfaAction, CfaPrec<P>> abstractor = BasicArgAbstractor.builder(
                            argBuilder)
                    .waitlist(PriorityWaitlist.create(search.getComp(cfa, errLoc)))
                    .stopCriterion(refinement.getStopCriterion())
                    .logger(logger).build();
            final ArgRefiner<CfaState<S>, CfaAction, CfaPrec<P>> refiner = refinement.getRefiner(this);
            final SafetyChecker<ARG<CfaState<S>, CfaAction>, Trace<CfaState<S>, CfaAction>, CfaPrec<P>> checker = ArgCegarChecker.create(
                    abstractor, refiner,
                    logger);
            return CfaConfig.create(checker, createInitPrec());
        }

        public MultiAnalysisSide<CfaState<S>, S, CfaState<UnitState>, CfaAction, CfaPrec<P>, CfaPrec<UnitPrec>> getMultiSide() {
            return new MultiAnalysisSide<>(
                    getAnalysis(),
                    CfaControlInitFuncKt.cfaControlInitFunc(cfa.getInitLoc()),
                    CfaCombineExtractUtilsKt::cfaCombineStates,
                    CfaCombineExtractUtilsKt::cfaExtractControlState,
                    CfaCombineExtractUtilsKt::cfaExtractDataState,
                    CfaCombineExtractUtilsKt::cfaExtractControlPrec);
        }
    }

    public final class ExplStrategy extends BuilderStrategy<ExplState, ExplPrec> {

        public ExplStrategy(CFA cfa) {
            super(cfa);
        }

        @Override
        public Set<Domain> getSupportedDomains() {
            return Set.of(Domain.EXPL);
        }

        @Override
        public Set<Refinement> getSupportedRefinements() {
            return Set.of(Refinement.values());
        }

        @Override
        public Set<InitPrec> getSupportedInitPrecs() {
            return Set.of(InitPrec.EMPTY, InitPrec.ALLVARS);
        }

        @Override
        public Analysis<ExplState, StmtAction, ? super ExplPrec> getDataAnalysis() {
            return ExplStmtAnalysis.create(abstractionSolverFactory.createSolver(), True(), maxEnum);
        }

        @Override
        public RefutationToPrec<ExplPrec, ItpRefutation> getItpRefToPrec() {
            return new ItpRefToExplPrec();
        }

        @Override
        public RefutationToPrec<ExplPrec, VarsRefutation> getVarsRefToPrec() {
            return new VarsRefToExplPrec();
        }

        @Override
        public CfaPrec<ExplPrec> createInitPrec() {
            return switch (initPrec) {
                case EMPTY -> precGranularity.createPrec(ExplPrec.empty());
                case ALLVARS -> precGranularity.createPrec(ExplPrec.of(cfa.getVars()));
                default ->
                        throw new UnsupportedOperationException(String.format(UNSUPPORTED_CONFIG_VALUE, getClass().getSimpleName(), initPrec, "initial precision"));
            };
        }
    }

    public final class PredStrategy extends BuilderStrategy<PredState, PredPrec> {

        public PredStrategy(CFA cfa) {
            super(cfa);
        }

        @Override
        public Set<Domain> getSupportedDomains() {
            return Set.of(Domain.PRED_BOOL, Domain.PRED_CART, Domain.PRED_SPLIT);
        }

        @Override
        public Set<Refinement> getSupportedRefinements() {
            return Set.of(
                    Refinement.FW_BIN_ITP,
                    Refinement.BW_BIN_ITP,
                    Refinement.SEQ_ITP,
                    Refinement.MULTI_SEQ,
                    Refinement.UCB,
                    Refinement.NWT_SP,
                    Refinement.NWT_WP,
                    Refinement.NWT_SP_LV,
                    Refinement.NWT_WP_LV,
                    Refinement.NWT_IT_SP,
                    Refinement.NWT_IT_WP,
                    Refinement.NWT_IT_SP_LV,
                    Refinement.NWT_IT_WP_LV
            );
        }

        @Override
        public Set<InitPrec> getSupportedInitPrecs() {
            return Set.of(InitPrec.EMPTY, InitPrec.ALLASSUMES);
        }

        @Override
        public Analysis<PredState, StmtAction, ? super PredPrec> getDataAnalysis() {
            Solver solver = abstractionSolverFactory.createSolver();
            return PredAnalysis.create(solver, domain.predAbstractorFunction.apply(solver), True());
        }

        @Override
        public RefutationToPrec<PredPrec, ItpRefutation> getItpRefToPrec() {
            return new ItpRefToPredPrec(predSplit.splitter);
        }

        @Override
        public CfaPrec<PredPrec> createInitPrec() {
            return switch (initPrec) {
                case EMPTY -> precGranularity.createPrec(PredPrec.of());
                case ALLASSUMES -> precGranularity.assumePrecs(cfa);
                default ->
                        throw new UnsupportedOperationException(String.format(UNSUPPORTED_CONFIG_VALUE, getClass().getSimpleName(), initPrec, "initial precision"));
            };
        }
    }

}
