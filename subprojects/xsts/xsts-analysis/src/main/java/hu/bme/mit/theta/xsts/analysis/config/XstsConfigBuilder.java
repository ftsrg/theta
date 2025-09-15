/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgCegarChecker;
import hu.bme.mit.theta.analysis.algorithm.cegar.ArgRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicArgAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterion;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStatePredicate;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.prod2explpred.*;
import hu.bme.mit.theta.analysis.stmtoptimizer.DefaultStmtOptimizer;
import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.unit.UnitState;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsNewAtomsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsNewOperandsAutoExpl;
import hu.bme.mit.theta.xsts.analysis.autoexpl.XstsStaticAutoExpl;
import hu.bme.mit.theta.xsts.analysis.initprec.*;
import hu.bme.mit.theta.xsts.analysis.util.XstsCombineExtractUtilsKt;
import hu.bme.mit.theta.xsts.analysis.util.XstsControlInitFuncKt;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

public class XstsConfigBuilder {

    //////////// CEGAR configuration ////////////

    public enum Domain {
        EXPL(null),
        PRED_BOOL(PredAbstractors::booleanAbstractor),
        PRED_CART(PredAbstractors::cartesianAbstractor),
        PRED_SPLIT(PredAbstractors::booleanSplitAbstractor),
        EXPL_PRED_BOOL(PredAbstractors::booleanAbstractor),
        EXPL_PRED_CART(PredAbstractors::cartesianAbstractor),
        EXPL_PRED_SPLIT(PredAbstractors::booleanSplitAbstractor),
        EXPL_PRED_COMBINED(null);

        public final Function<Solver, PredAbstractor> predAbstractorFunction;

        Domain(final Function<Solver, PredAbstractor> predAbstractorFunction) {
            this.predAbstractorFunction = predAbstractorFunction;
        }
    }

    public enum Refinement {
        FW_BIN_ITP {
            @Override
            public ExprTraceChecker<ItpRefutation> getItpExprTraceChecker(
                    Expr<BoolType> init, Expr<BoolType> target, ItpSolver solver) {
                return ExprTraceFwBinItpChecker.create(init, target, solver);
            }
        },
        BW_BIN_ITP {
            @Override
            public ExprTraceChecker<ItpRefutation> getItpExprTraceChecker(
                    Expr<BoolType> init, Expr<BoolType> target, ItpSolver solver) {
                return ExprTraceBwBinItpChecker.create(init, target, solver);
            }
        },
        SEQ_ITP {
            @Override
            public ExprTraceChecker<ItpRefutation> getItpExprTraceChecker(
                    Expr<BoolType> init, Expr<BoolType> target, ItpSolver solver) {
                return ExprTraceSeqItpChecker.create(init, target, solver);
            }
        },
        UNSAT_CORE,
        MULTI_SEQ {
            @Override
            public <S extends ExprState> StopCriterion<S, XstsAction> getStopCriterion() {
                return StopCriterions.fullExploration();
            }

            @Override
            public ExprTraceChecker<ItpRefutation> getItpExprTraceChecker(
                    Expr<BoolType> init, Expr<BoolType> target, ItpSolver solver) {
                return ExprTraceSeqItpChecker.create(init, target, solver);
            }

            @Override
            public <S extends ExprState, P extends Prec, R extends Refutation>
                    ArgRefiner<XstsState<S>, XstsAction, P> createRefiner(
                            ExprTraceChecker<R> traceChecker,
                            RefutationToPrec<P, R> refToPrec,
                            PruneStrategy pruneStrategy,
                            Logger logger) {
                return MultiExprTraceRefiner.create(
                        traceChecker, JoiningPrecRefiner.create(refToPrec), pruneStrategy, logger);
            }
        };

        public <S extends ExprState> StopCriterion<S, XstsAction> getStopCriterion() {
            return StopCriterions.firstCex();
        }

        public ExprTraceChecker<ItpRefutation> getItpExprTraceChecker(
                final Expr<BoolType> init, final Expr<BoolType> target, final ItpSolver solver) {
            throw new UnsupportedOperationException(
                    String.format(
                            "%s domain can't provide trace checker of ItpRefutation",
                            this.getClass().getSimpleName()));
        }

        public <S extends ExprState, P extends Prec, R extends Refutation>
                ArgRefiner<XstsState<S>, XstsAction, P> createRefiner(
                        ExprTraceChecker<R> traceChecker,
                        RefutationToPrec<P, R> refToPrec,
                        PruneStrategy pruneStrategy,
                        Logger logger) {
            return SingleExprTraceRefiner.create(
                    traceChecker, JoiningPrecRefiner.create(refToPrec), pruneStrategy, logger);
        }
    }

    public enum Search {
        BFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.bfs())),

        DFS(ArgNodeComparators.combine(ArgNodeComparators.targetFirst(), ArgNodeComparators.dfs()));

        public final ArgNodeComparators.ArgNodeComparator comparator;

        Search(final ArgNodeComparators.ArgNodeComparator comparator) {
            this.comparator = comparator;
        }
    }

    public enum PredSplit {
        WHOLE(ExprSplitters.whole()),

        CONJUNCTS(ExprSplitters.conjuncts()),

        ATOMS(ExprSplitters.atoms());

        public final ExprSplitters.ExprSplitter splitter;

        PredSplit(final ExprSplitters.ExprSplitter splitter) {
            this.splitter = splitter;
        }
    }

    public enum InitPrec {
        EMPTY(new XstsEmptyInitPrec()),

        PROP(new XstsPropInitPrec()),

        CTRL(new XstsCtrlInitPrec()),

        ALLVARS(new XstsAllVarsInitPrec());

        public final XstsInitPrec builder;

        InitPrec(final XstsInitPrec builder) {
            this.builder = builder;
        }
    }

    public enum AutoExpl {
        STATIC(new XstsStaticAutoExpl()),

        NEWATOMS(new XstsNewAtomsAutoExpl()),

        NEWOPERANDS(new XstsNewOperandsAutoExpl());

        public final XstsAutoExpl builder;

        AutoExpl(final XstsAutoExpl builder) {
            this.builder = builder;
        }
    }

    public enum OptimizeStmts {
        ON,
        OFF
    }

    private Logger logger = NullLogger.getInstance();
    private final SolverFactory abstractionSolverFactory;
    private final SolverFactory refinementSolverFactory;
    private final Domain domain;
    private final Refinement refinement;
    private Search search = Search.BFS;
    private PredSplit predSplit = PredSplit.WHOLE;
    private int maxEnum = 0;
    private InitPrec initPrec = InitPrec.EMPTY;
    private PruneStrategy pruneStrategy = PruneStrategy.LAZY;
    private OptimizeStmts optimizeStmts = OptimizeStmts.ON;
    private AutoExpl autoExpl = AutoExpl.NEWOPERANDS;

    public XstsConfigBuilder(
            final Domain domain,
            final Refinement refinement,
            final SolverFactory abstractionSolverFactory,
            final SolverFactory refinementSolverFactory) {
        this.domain = domain;
        this.refinement = refinement;
        this.abstractionSolverFactory = abstractionSolverFactory;
        this.refinementSolverFactory = refinementSolverFactory;
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
        if (domain == Domain.EXPL) {
            return (new ExplStrategy(xsts)).buildConfig();
        }
        if (domain == Domain.PRED_BOOL
                || domain == Domain.PRED_CART
                || domain == Domain.PRED_SPLIT) {
            return (new PredStrategy(xsts)).buildConfig();
        }
        if (domain == Domain.EXPL_PRED_BOOL
                || domain == Domain.EXPL_PRED_CART
                || domain == Domain.EXPL_PRED_SPLIT
                || domain == Domain.EXPL_PRED_COMBINED) {
            return (new ProdStrategy(xsts)).buildConfig();
        }
        throw new UnsupportedOperationException(domain + " domain is not supported.");
    }

    public abstract class BuilderStrategy<S extends ExprState, P extends Prec> {

        protected static final String UNSUPPORTED_CONFIG_VALUE =
                "Builder strategy %s does not support configuration value %s as %s";
        protected final XSTS xsts;
        protected final Solver abstractionSolver;
        protected final Expr<BoolType> negProp;

        @SuppressWarnings("java:S1699")
        protected BuilderStrategy(XSTS xsts) {
            checkState(
                    getSupportedDomains().contains(domain),
                    UNSUPPORTED_CONFIG_VALUE,
                    getClass().getSimpleName(),
                    domain,
                    "domain");
            checkState(
                    getSupportedRefinements().contains(refinement),
                    UNSUPPORTED_CONFIG_VALUE,
                    getClass().getSimpleName(),
                    refinement,
                    "refinement");
            this.xsts = xsts;
            abstractionSolver = abstractionSolverFactory.createSolver();
            negProp = Not(xsts.getProp());
        }

        abstract Set<Domain> getSupportedDomains();

        abstract Set<Refinement> getSupportedRefinements();

        abstract StmtOptimizer<S> getLtsOptimizer();

        StmtOptimizer<S> optimizer() {
            if (optimizeStmts == OptimizeStmts.OFF) {
                return DefaultStmtOptimizer.create();
            }
            return getLtsOptimizer();
        }

        public LTS<XstsState<S>, XstsAction> getLts() {
            return XstsLts.create(xsts, XstsStmtOptimizer.create(optimizer()));
        }

        public abstract Predicate<XstsState<S>> getPredicate();

        public abstract Analysis<S, StmtAction, ? super P> getDataAnalysis();

        public XstsAnalysis<S, P> getAnalysis() {
            return XstsAnalysis.create(getDataAnalysis());
        }

        public abstract RefutationToPrec<P, ItpRefutation> getItpRefToPrec();

        public ArgRefiner<XstsState<S>, XstsAction, P> getRefiner() {
            return refinement.createRefiner(
                    refinement.getItpExprTraceChecker(
                            xsts.getInitFormula(),
                            negProp,
                            refinementSolverFactory.createItpSolver()),
                    getItpRefToPrec(),
                    pruneStrategy,
                    logger);
        }

        public abstract P getInitPrec();

        XstsConfig<XstsState<S>, XstsAction, P> buildConfig() {
            final LTS<XstsState<S>, XstsAction> lts = getLts();
            final Predicate<XstsState<S>> target = getPredicate();
            final Analysis<XstsState<S>, XstsAction, P> analysis = getAnalysis();
            final ArgBuilder<XstsState<S>, XstsAction, P> argBuilder =
                    ArgBuilder.create(lts, analysis, target, true);
            final ArgAbstractor<XstsState<S>, XstsAction, P> abstractor =
                    BasicArgAbstractor.builder(argBuilder)
                            .waitlist(PriorityWaitlist.create(search.comparator))
                            .stopCriterion(refinement.getStopCriterion())
                            .logger(logger)
                            .build();
            final ArgRefiner<XstsState<S>, XstsAction, P> refiner = getRefiner();
            final SafetyChecker<ARG<XstsState<S>, XstsAction>, Trace<XstsState<S>, XstsAction>, P>
                    checker = ArgCegarChecker.create(abstractor, refiner, logger);
            return XstsConfig.create(checker, getInitPrec());
        }

        public MultiAnalysisSide<XstsState<S>, S, XstsState<UnitState>, XstsAction, P, UnitPrec>
                getMultiSide() {
            return new MultiAnalysisSide<>(
                    getAnalysis(),
                    XstsControlInitFuncKt.xstsControlInitFunc(),
                    XstsCombineExtractUtilsKt::xstsCombineStates,
                    XstsCombineExtractUtilsKt::xstsExtractControlState,
                    XstsCombineExtractUtilsKt::xstsExtractDataState,
                    XstsCombineExtractUtilsKt::xstsExtractControlPrec);
        }
    }

    public class ExplStrategy extends BuilderStrategy<ExplState, ExplPrec> {

        @Override
        Set<Domain> getSupportedDomains() {
            return new HashSet<>(List.of(Domain.EXPL));
        }

        @Override
        Set<Refinement> getSupportedRefinements() {
            return new HashSet<>(List.of(Refinement.values()));
        }

        public ExplStrategy(XSTS xsts) {
            super(xsts);
            checkState(
                    domain == Domain.EXPL,
                    UNSUPPORTED_CONFIG_VALUE,
                    this.getClass().getSimpleName(),
                    domain,
                    "domain");
        }

        @Override
        public StmtOptimizer<ExplState> getLtsOptimizer() {
            return ExplStmtOptimizer.getInstance();
        }

        @Override
        public Predicate<XstsState<ExplState>> getPredicate() {
            return new XstsStatePredicate<>(new ExplStatePredicate(negProp, abstractionSolver));
        }

        @Override
        public Analysis<ExplState, StmtAction, ExplPrec> getDataAnalysis() {
            return ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), maxEnum);
        }

        @Override
        public RefutationToPrec<ExplPrec, ItpRefutation> getItpRefToPrec() {
            return new ItpRefToExplPrec();
        }

        @Override
        public ArgRefiner<XstsState<ExplState>, XstsAction, ExplPrec> getRefiner() {
            if (refinement == Refinement.UNSAT_CORE) {
                return SingleExprTraceRefiner.create(
                        ExprTraceUnsatCoreChecker.create(
                                xsts.getInitFormula(),
                                negProp,
                                refinementSolverFactory.createUCSolver()),
                        JoiningPrecRefiner.create(new VarsRefToExplPrec()),
                        pruneStrategy,
                        logger);
            }
            return super.getRefiner();
        }

        @Override
        public ExplPrec getInitPrec() {
            return initPrec.builder.createExpl(xsts);
        }
    }

    public class PredStrategy extends BuilderStrategy<PredState, PredPrec> {
        @Override
        Set<Domain> getSupportedDomains() {
            return new HashSet<>(List.of(Domain.PRED_CART, Domain.PRED_BOOL, Domain.PRED_SPLIT));
        }

        @Override
        Set<Refinement> getSupportedRefinements() {
            return new HashSet<>(
                    List.of(
                            Refinement.FW_BIN_ITP,
                            Refinement.BW_BIN_ITP,
                            Refinement.SEQ_ITP,
                            Refinement.MULTI_SEQ));
        }

        public PredStrategy(XSTS xsts) {
            super(xsts);
            checkState(
                    domain == Domain.PRED_BOOL
                            || domain == Domain.PRED_SPLIT
                            || domain == Domain.PRED_CART,
                    UNSUPPORTED_CONFIG_VALUE,
                    this.getClass().getSimpleName(),
                    domain,
                    "domain");
        }

        @Override
        StmtOptimizer<PredState> getLtsOptimizer() {
            return PredStmtOptimizer.getInstance();
        }

        @Override
        public Predicate<XstsState<PredState>> getPredicate() {
            return new XstsStatePredicate<>(new ExprStatePredicate(negProp, abstractionSolver));
        }

        @Override
        public Analysis<PredState, StmtAction, PredPrec> getDataAnalysis() {
            return PredAnalysis.create(
                    abstractionSolver,
                    domain.predAbstractorFunction.apply(abstractionSolver),
                    xsts.getInitFormula());
        }

        @Override
        public RefutationToPrec<PredPrec, ItpRefutation> getItpRefToPrec() {
            return new ItpRefToPredPrec(predSplit.splitter);
        }

        @Override
        public PredPrec getInitPrec() {
            return initPrec.builder.createPred(xsts);
        }
    }

    public class ProdStrategy
            extends BuilderStrategy<
                    Prod2State<ExplState, PredState>, Prod2Prec<ExplPrec, PredPrec>> {

        @Override
        Set<Domain> getSupportedDomains() {
            return new HashSet<>(
                    List.of(
                            Domain.EXPL_PRED_BOOL,
                            Domain.EXPL_PRED_CART,
                            Domain.EXPL_PRED_SPLIT,
                            Domain.EXPL_PRED_COMBINED));
        }

        @Override
        Set<Refinement> getSupportedRefinements() {
            return new HashSet<>(
                    List.of(
                            Refinement.FW_BIN_ITP,
                            Refinement.BW_BIN_ITP,
                            Refinement.SEQ_ITP,
                            Refinement.MULTI_SEQ));
        }

        public ProdStrategy(XSTS xsts) {
            super(xsts);
            checkState(
                    domain == Domain.EXPL_PRED_BOOL
                            || domain == Domain.EXPL_PRED_SPLIT
                            || domain == Domain.EXPL_PRED_CART
                            || domain == Domain.EXPL_PRED_COMBINED,
                    UNSUPPORTED_CONFIG_VALUE,
                    this.getClass().getSimpleName(),
                    domain,
                    "domain");
            checkState(
                    refinement != Refinement.UNSAT_CORE,
                    UNSUPPORTED_CONFIG_VALUE,
                    getClass().getSimpleName(),
                    refinement,
                    "refinement");
        }

        @Override
        StmtOptimizer<Prod2State<ExplState, PredState>> getLtsOptimizer() {
            return Prod2ExplPredStmtOptimizer.create(ExplStmtOptimizer.getInstance());
        }

        @Override
        public Predicate<XstsState<Prod2State<ExplState, PredState>>> getPredicate() {
            return new XstsStatePredicate<>(new ExprStatePredicate(negProp, abstractionSolver));
        }

        @Override
        public Analysis<Prod2State<ExplState, PredState>, StmtAction, Prod2Prec<ExplPrec, PredPrec>>
                getDataAnalysis() {
            if (domain == Domain.EXPL_PRED_BOOL
                    || domain == Domain.EXPL_PRED_CART
                    || domain == Domain.EXPL_PRED_SPLIT) {
                final PredAbstractors.PredAbstractor predAbstractor =
                        domain.predAbstractorFunction.apply(abstractionSolver);
                return Prod2Analysis.create(
                        ExplStmtAnalysis.create(abstractionSolver, xsts.getInitFormula(), maxEnum),
                        PredAnalysis.create(
                                abstractionSolver, predAbstractor, xsts.getInitFormula()),
                        Prod2ExplPredPreStrengtheningOperator.create(),
                        Prod2ExplPredStrengtheningOperator.create(abstractionSolver));
            } else {
                final Prod2ExplPredAbstractors.Prod2ExplPredAbstractor prodAbstractor =
                        Prod2ExplPredAbstractors.booleanAbstractor(abstractionSolver);
                return Prod2ExplPredAnalysis.create(
                        ExplAnalysis.create(abstractionSolver, xsts.getInitFormula()),
                        PredAnalysis.create(
                                abstractionSolver,
                                PredAbstractors.booleanAbstractor(abstractionSolver),
                                xsts.getInitFormula()),
                        Prod2ExplPredStrengtheningOperator.create(abstractionSolver),
                        prodAbstractor);
            }
        }

        @Override
        public RefutationToPrec<Prod2Prec<ExplPrec, PredPrec>, ItpRefutation> getItpRefToPrec() {
            return AutomaticItpRefToProd2ExplPredPrec.create(
                    autoExpl.builder.create(xsts), predSplit.splitter);
        }

        @Override
        public Prod2Prec<ExplPrec, PredPrec> getInitPrec() {
            return initPrec.builder.createProd2ExplPred(xsts);
        }
    }
}
