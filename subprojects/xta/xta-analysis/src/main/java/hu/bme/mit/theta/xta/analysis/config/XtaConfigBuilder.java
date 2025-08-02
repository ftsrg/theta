package hu.bme.mit.theta.xta.analysis.config;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
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
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.xta.XtaProcess;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.xta.analysis.XtaLts;
import hu.bme.mit.theta.xta.analysis.XtaState;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.xta.analysis.prec.*;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XtaConfigBuilder {
    public enum Domain {
        EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT
    }

    public enum Refinement {
        FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE, UCB,
        NWT_WP, NWT_SP, NWT_WP_LV, NWT_SP_LV, NWT_IT_WP, NWT_IT_SP, NWT_IT_WP_LV, NWT_IT_SP_LV
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
    //TODO more InitPrec needed
    public enum InitPrec{
        EMPTY(new XtaEmptyInitPrec());
        public final XtaInitPrec builder;
        private InitPrec(final XtaInitPrec _builder){
            builder = _builder;
        }
    }
    public enum PrecGranularity{
        GLOBAL {

            public <P extends Prec> XtaPrec<P> createPrec(final P innerPrec) {
                return GlobalXtaPrec.create(innerPrec);
            }


            public <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XtaState<S>, A, XtaPrec<P>, R> createRefiner(
                    final RefutationToPrec<P, R> refToPrec) {
                return GlobalXtaPrecRefiner.create(refToPrec);
            }
        },
        LOCAL {

            public <P extends Prec> XtaPrec<P> createPrec(final P innerPrec) {
                return GlobalXtaPrec.create(innerPrec);
            }


            public <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XtaState<S>, A, XtaPrec<P>, R> createRefiner(
            final RefutationToPrec<P, R> refToPrec) {
                return GlobalXtaPrecRefiner.create(refToPrec);
            }
        };
        public abstract <P extends Prec> XtaPrec<P> createPrec(final P innerPrec);
        public abstract  <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> PrecRefiner<XtaState<S>, A, XtaPrec<P>, R> createRefiner(
                final RefutationToPrec<P, R> refToPrec);


    }


    private Logger logger = NullLogger.getInstance();
    private final SolverFactory abstractionSolverFactory;
    private final SolverFactory refinementSolverFactory;
    private final Domain domain;
    private final Refinement refinement;
    private Search search = Search.BFS;
    private PredSplit predSplit = PredSplit.WHOLE;
    private PrecGranularity precGranularity = PrecGranularity.GLOBAL;
    private int maxEnum = 0;
    private InitPrec initPrec = InitPrec.EMPTY;
    private PruneStrategy pruneStrategy = PruneStrategy.LAZY;


    public XtaConfigBuilder(final Domain domain, final Refinement refinement, final SolverFactory solverFactory) {
        this.domain = domain;
        this.refinement = refinement;
        this.abstractionSolverFactory = solverFactory;
        this.refinementSolverFactory = solverFactory;
    }
    public XtaConfigBuilder(final Domain domain, final Refinement refinement, final SolverFactory abstractionSolverFactory, final SolverFactory refinementSolverFactory) {
        this.domain = domain;
        this.refinement = refinement;
        this.abstractionSolverFactory = abstractionSolverFactory;
        this.refinementSolverFactory = refinementSolverFactory;
    }
    public XtaConfigBuilder logger(final Logger logger) {
        this.logger = logger;
        return this;
    }
    public XtaConfigBuilder search(final Search search) {
        this.search = search;
        return this;
    }
    public XtaConfigBuilder predSplit(final PredSplit predSplit) {
        this.predSplit = predSplit;
        return this;
    }
    public XtaConfigBuilder precGranularity(final PrecGranularity precGranularity) {
        this.precGranularity = precGranularity;

        return this;
    }
    public XtaConfigBuilder maxEnum(final int maxEnum) {
        this.maxEnum = maxEnum;
        return this;
    }
    public XtaConfigBuilder initPrec(final InitPrec initPrec) {
        this.initPrec = initPrec;
        return this;
    }
    public XtaConfigBuilder pruneStrategy(final PruneStrategy pruneStrategy) {
        this.pruneStrategy = pruneStrategy;
        return this;
    }
    public XtaConfig<? extends State, ? extends Action, ? extends Prec> build(final XtaSystem xta, final XtaProcess.Loc errLoc) {
        final XtaLts lts = XtaLts.create(xta);
        //final Expr<BoolType> negProp = xta.
        if(domain == Domain.PRED_BOOL || domain == Domain.PRED_CART || domain == Domain.PRED_SPLIT){
            final Solver analysisSolver = abstractionSolverFactory.createSolver();
            PredAbstractors.PredAbstractor predAbstractor;
            switch (domain) {
                case PRED_BOOL:
                    predAbstractor = PredAbstractors.booleanAbstractor(analysisSolver);
                    break;
                case PRED_SPLIT:
                    predAbstractor = PredAbstractors.booleanSplitAbstractor(analysisSolver);
                    break;
                case PRED_CART:
                    predAbstractor = PredAbstractors.cartesianAbstractor(analysisSolver);
                    break;
                default:
                    throw new UnsupportedOperationException(domain + " domain is not supported.");
            }
            final Analysis<Prod2State<PredState, ZoneState>, XtaAction, Prod2Prec<PredPrec, ZonePrec>> prod2Analysis = Prod2Analysis.create(
                    PredAnalysis.create(analysisSolver, predAbstractor, xta.getInitVal().toExpr()),
                    XtaZoneAnalysis.create(xta.getInitLocs())
            );
            //miért nem kell xtaprec-be becsomagolni
            final Analysis<XtaState<Prod2State<PredState, ZoneState>>, XtaAction, Prod2Prec<PredPrec, ZonePrec>> analysis = XtaAnalysis.create(xta,prod2Analysis);

            //TODO analysis
            final ArgBuilder<XtaState<Prod2State<PredState, ZoneState>>,XtaAction,Prod2Prec<PredPrec, ZonePrec> > argbuilder = ArgBuilder.create(lts, analysis, s -> s.getLocs().stream().anyMatch(l -> l.getKind().equals(XtaProcess.LocKind.ERROR)), true);
            final Abstractor<XtaState<Prod2State<PredState, ZoneState>>, XtaAction, Prod2Prec<PredPrec, ZonePrec>> abstractor = BasicAbstractor.builder(argbuilder)
                    .waitlist(PriorityWaitlist.create(search.comparator))
                    .stopCriterion(refinement == Refinement.MULTI_SEQ ? StopCriterions.fullExploration() : StopCriterions.firstCex())
                    .logger(logger).build()
                    ;

            ExprTraceChecker<ItpRefutation> exprTraceChecker;
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
            final RefutationToPrec<Prod2Prec<PredPrec, ZonePrec>, ItpRefutation> reftoprec = ItpRefToProd2PredZonePrec.create(predSplit.splitter, ZonePrec.of(xta.getClockVars()));
            Refiner<XtaState<Prod2State<PredState, ZoneState>>, XtaAction, Prod2Prec<PredPrec, ZonePrec>> refiner;

            PrecRefiner<XtaState<Prod2State<PredState, ZoneState>>, XtaAction, Prod2Prec<PredPrec, ZonePrec>, ItpRefutation> precRefiner
                    = JoiningPrecRefiner.create(reftoprec);
            if (refinement == Refinement.MULTI_SEQ) {

                refiner = MultiExprTraceRefiner.create(exprTraceChecker, precRefiner, pruneStrategy, logger);
            } else {
                refiner = SingleExprTraceRefiner.create(exprTraceChecker,
                        precRefiner, pruneStrategy, logger);
            }

            final SafetyChecker<XtaState<Prod2State<PredState, ZoneState>>, XtaAction, Prod2Prec<PredPrec, ZonePrec>> checker = CegarChecker.create(
                    abstractor,refiner, logger);

            Prod2Prec<PredPrec, ZonePrec> prec = initPrec.builder.createProd2PredZone(xta);
            return XtaConfig.create(checker, prec);
        }
        //TODO :
        // Only works with Prod2Prec<PredPrec, ZonePrec>

        return null;
    }

}
