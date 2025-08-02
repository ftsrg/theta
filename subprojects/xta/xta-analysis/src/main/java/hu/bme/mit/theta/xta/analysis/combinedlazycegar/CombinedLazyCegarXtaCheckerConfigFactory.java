package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.pred.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.*;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaLensUtils;
import hu.bme.mit.theta.xta.analysis.lazy.LuZoneStrategy2;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneInvTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaUtils.forceCast;
import static hu.bme.mit.theta.xta.analysis.lazy.LazyXtaLensUtils.createConcrProd2Lens;

@SuppressWarnings({"rawtypes", "unchecked"})
public class CombinedLazyCegarXtaCheckerConfigFactory {

    public enum DataDomain {
        EXPL, PRED_BOOL, PRED_CART, PRED_SPLIT
    }

    @SuppressWarnings("unused")
    public enum PredSplit {
        WHOLE(ExprSplitters.whole()),

        CONJUNCTS(ExprSplitters.conjuncts()),

        ATOMS(ExprSplitters.atoms());

        public final ExprSplitters.ExprSplitter splitter;

        PredSplit(final ExprSplitters.ExprSplitter splitter) {
            this.splitter = splitter;
        }
    }

    public enum DataRefinement {
        FW_BIN_ITP, BW_BIN_ITP, SEQ_ITP, MULTI_SEQ, UNSAT_CORE, UCB,
        NWT_WP, NWT_SP, NWT_WP_LV, NWT_SP_LV, NWT_IT_WP, NWT_IT_SP, NWT_IT_WP_LV, NWT_IT_SP_LV
    }

    private final XtaSystem system;
    private final Logger logger;
    private final SolverFactory solverFactory;
    private DataDomain dataDomain = DataDomain.EXPL;
    private int maxEnum = 0;
    private PredSplit predSplit = PredSplit.WHOLE;
    private DataRefinement dataRefinement = DataRefinement.SEQ_ITP;
    private ClockStrategy clockStrategy = ClockStrategy.BWITP;
    private SearchStrategy searchStrategy = SearchStrategy.BFS;
    private PruneStrategy pruneStrategy = PruneStrategy.FULL;

    private CombinedLazyCegarXtaCheckerConfigFactory(final XtaSystem system, final Logger logger, final SolverFactory solverFactory) {
        this.system = system;
        this.logger = logger;
        this.solverFactory = solverFactory;
    }

    private CombinedLazyCegarXtaCheckerConfigFactory(final XtaSystem system) {
        this(system, NullLogger.getInstance(), Z3SolverFactory.getInstance());
    }

    public static CombinedLazyCegarXtaCheckerConfigFactory create(final XtaSystem system, final Logger logger, final SolverFactory solverFactory) {
        return new CombinedLazyCegarXtaCheckerConfigFactory(system, logger, solverFactory);
    }

    public static CombinedLazyCegarXtaCheckerConfigFactory create(final XtaSystem system) {
        return new CombinedLazyCegarXtaCheckerConfigFactory(system);
    }

    public CombinedLazyCegarXtaCheckerConfigFactory dataDomain(final DataDomain dataDomain) {
        this.dataDomain = dataDomain;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory maxEnum(final int maxEnum) {
        this.maxEnum = maxEnum;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory predSplit(final PredSplit predSplit) {
        this.predSplit = predSplit;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory dataRefinement(final DataRefinement dataRefinement) {
        this.dataRefinement = dataRefinement;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory clockStrategy(final ClockStrategy clockStrategy) {
        this.clockStrategy = clockStrategy;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory searchStragegy(final SearchStrategy searchStrategy) {
        this.searchStrategy = searchStrategy;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfigFactory pruneStrategy(final PruneStrategy pruneStrategy) {
        this.pruneStrategy = pruneStrategy;
        return this;
    }

    public CombinedLazyCegarXtaCheckerConfig build() {
        final var lazyStrategy = createLazyStrategy();

        final var lazyAnalysis = createLazyAnalysis(
            lazyStrategy.getPartialOrd(),
            lazyStrategy.getInitAbstractor()
        );

        final var prec = createConcrPrec();

        final var cegarChecker = CegarChecker.create(
            new LazyAbstractor<>(
                forceCast(XtaLts.create(system)),
                searchStrategy,
                lazyStrategy,
                lazyAnalysis,
                XtaState::isError,
                createConcrProd2Lens()
            ),
            SingleExprTraceRefiner.create(
                new CombinedLazyCegarExprTraceChecker(
                    switch (dataRefinement) {
                        case FW_BIN_ITP -> ExprTraceFwBinItpChecker.create(True(), True(), solverFactory.createItpSolver());
                        case BW_BIN_ITP -> ExprTraceBwBinItpChecker.create(True(), True(), solverFactory.createItpSolver());
                        case SEQ_ITP, MULTI_SEQ -> ExprTraceSeqItpChecker.create(True(), True(), solverFactory.createItpSolver());
                        case UNSAT_CORE -> ExprTraceUnsatCoreChecker.create(True(), True(), solverFactory.createUCSolver());
                        case UCB -> ExprTraceUCBChecker.create(True(), True(), solverFactory.createUCSolver());
                        case NWT_WP -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withoutIT().withWP().withoutLV();
                        case NWT_SP -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withoutIT().withSP().withoutLV();
                        case NWT_WP_LV -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withoutIT().withWP().withLV();
                        case NWT_SP_LV -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withoutIT().withSP().withLV();
                        case NWT_IT_WP -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withIT().withWP().withoutLV();
                        case NWT_IT_SP -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withIT().withSP().withoutLV();
                        case NWT_IT_WP_LV -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withIT().withWP().withLV();
                        case NWT_IT_SP_LV -> ExprTraceNewtonChecker.create(True(), True(), solverFactory.createUCSolver()).withIT().withSP().withLV();
                    },
                    createConcrProd2Lens(),
                    system
                ),
                new CombinedLazyCegarXtaPrecRefiner(switch (dataDomain) {
                    case EXPL -> new ItpRefToExplPrec();
                    case PRED_BOOL, PRED_CART, PRED_SPLIT -> new ItpRefToPredPrec(predSplit.splitter);
                }),
                pruneStrategy,
                logger
            ),
            logger
        );

        return new CombinedLazyCegarXtaCheckerConfig<>(cegarChecker, prec);
    }

    private LazyAnalysis createLazyAnalysis(final PartialOrd<Prod2State<ExplState, ZoneState>> abstrPartialOrd,
                       final InitAbstractor<Prod2State<ExplState, ZoneState>, Prod2State<ExplState, ZoneState>> initAbstractor) {
        final Prod2Analysis prod2ConcrAnalysis = createConcrAnalysis();
        final XtaAnalysis xtaConcrAnalysis = XtaAnalysis.create(system, prod2ConcrAnalysis);

        return LazyAnalysis.create(
            XtaOrd.create(abstrPartialOrd),
            xtaConcrAnalysis.getInitFunc(),
            xtaConcrAnalysis.getTransFunc(),
            XtaInitAbstractor.create(initAbstractor)
        );
    }

    private Prod2Analysis createConcrAnalysis() {
        return Prod2Analysis.create(
            createConcrDataAnalysis(),
            createConcrClockAnalysis()
        );
    }

    private Analysis createConcrDataAnalysis() {
        return CombinedLazyCegarXtaAnalysis.create(
            forceCast(switch (dataDomain) {
                case EXPL -> ExplStmtAnalysis.create(
                    solverFactory.createSolver(),
                    system.getInitVal().toExpr(),
                    maxEnum
                );
                case PRED_BOOL -> PredAnalysis.create(
                    solverFactory.createSolver(),
                    PredAbstractors.booleanAbstractor(solverFactory.createSolver()),
                    system.getInitVal().toExpr()
                );
                case PRED_CART -> PredAnalysis.create(
                    solverFactory.createSolver(),
                    PredAbstractors.cartesianAbstractor(solverFactory.createSolver()),
                    system.getInitVal().toExpr()
                );
                case PRED_SPLIT -> PredAnalysis.create(
                    solverFactory.createSolver(),
                    PredAbstractors.booleanSplitAbstractor(solverFactory.createSolver()),
                    system.getInitVal().toExpr()
                );
            })
        );
    }

    private Analysis createConcrClockAnalysis() {
        return switch (clockStrategy) {
            case LU, FWITP, BWITP -> XtaZoneAnalysis.create(system.getInitLocs());
        };
    }

    private LazyStrategy createLazyStrategy() {
        final LazyStrategy dataLazyStrategy = forceCast(createDataStrategy2());
        final LazyStrategy clockLazyStrategy = forceCast(createClockStrategy());

        final Function<LazyState<XtaState<?>, XtaState<?>>, ?> projection = s -> Tuple3.of(
            s.getConcrState().getLocs(),
            dataLazyStrategy.getProjection().apply(s),
            clockLazyStrategy.getProjection().apply(s)
        );

        final Lens lens = createConcrProd2Lens();
        return new Prod2LazyStrategy<>(lens, dataLazyStrategy, clockLazyStrategy, projection);
    }

    private LazyStrategy createDataStrategy2() {
        return new BasicLazyStrategy<>(
            createDataLens(),
            createDataConcretizer()
        );
    }

    private Lens createDataLens() {
        return LazyXtaLensUtils.createConcrDataLens();
    }

    private Concretizer createDataConcretizer() {
        return BasicConcretizer.create(ExplOrd.getInstance());
    }

    private LazyStrategy createClockStrategy() {
        return switch (clockStrategy) {
            case BWITP, FWITP -> createLazyZoneStrategy();
            case LU -> {
                final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, LuZoneState>>>, LuZoneState>
                    lens = LazyXtaLensUtils.createAbstrClockLens();
                yield new LuZoneStrategy2<>(lens);
            }
        };
    }

    private LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction>
    createLazyZoneStrategy() {
        final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, LazyState<ZoneState, ZoneState>>
            lens = LazyXtaLensUtils.createLazyClockLens();
        final Lattice<ZoneState> lattice = ZoneLattice.getInstance();
        final Interpolator<ZoneState, ZoneState> interpolator = ZoneInterpolator.getInstance();
        final PartialOrd<ZoneState> partialOrd = ZoneOrd.getInstance();
        final Concretizer<ZoneState, ZoneState> concretizer = BasicConcretizer.create(partialOrd);
        final InvTransFunc<ZoneState, XtaAction, ZonePrec> zoneInvTransFunc = XtaZoneInvTransFunc.getInstance();
        final ZonePrec prec = ZonePrec.of(system.getClockVars());

        switch (clockStrategy){
            case BWITP:
                return new BwItpStrategy<>(lens, lattice, interpolator, concretizer, zoneInvTransFunc, prec);
            case FWITP:
                final TransFunc<ZoneState, XtaAction, ZonePrec> zoneTransFunc = XtaZoneTransFunc.getInstance();
                return new FwItpStrategy<>(lens, lattice, interpolator, concretizer, zoneInvTransFunc, prec, zoneTransFunc, prec);
            default:
                throw new AssertionError();
        }
    }

    private Prod2Prec createConcrPrec() {
        return Prod2Prec.of(createConcrDataPrec(), createConcrZonePrec());
    }

    private Prec createConcrDataPrec() {
        return switch (dataDomain) {
            case EXPL -> ExplPrec.empty();
            case PRED_BOOL, PRED_CART, PRED_SPLIT -> PredPrec.of();
        };
    }

    private ZonePrec createConcrZonePrec() {
        return ZonePrec.of(system.getClockVars());
    }

}
