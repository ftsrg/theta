package hu.bme.mit.theta.xta.analysis.combinedlazycegar;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.CegarChecker;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.*;
import hu.bme.mit.theta.xta.analysis.lazy.ClockStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaLensUtils;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneInvTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneTransFunc;

import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.xta.analysis.combinedlazycegar.CombinedLazyCegarXtaUtils.forceCast;
import static hu.bme.mit.theta.xta.analysis.lazy.LazyXtaLensUtils.createConcrProd2Lens;

public class CombinedLazyCegarXtaCheckerConfigFactory {
    private final XtaSystem system;
    private final Logger logger;
    private final SolverFactory solverFactory;

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

    public CombinedLazyCegarXtaCheckerConfig<ExplState, ZoneState, ExplState, ZoneState, ExplPrec, ZonePrec> build() {
        final var lazyStrategy = createLazyStrategy(ClockStrategy.BWITP);

        final var lazyAnalysis = createLazyAnalysis(
            solverFactory,
            lazyStrategy.getPartialOrd(),
            lazyStrategy.getInitAbstractor()
        );

        ArgCexCheckHandler.instance.setArgCexCheck(true, false);
        final var prec = createConcrPrec();

        final var cegarChecker = CegarChecker.create(
            new LazyAbstractor<>(
                forceCast(XtaLts.create(system)),
                SearchStrategy.BFS,
                lazyStrategy,
                lazyAnalysis,
                XtaState::isError,
                createConcrProd2Lens()
            ),
            SingleExprTraceRefiner.create(
                new CombinedLazyCegarExprTraceChecker<>(
                    ExprTraceSeqItpChecker.create(True(), True(), solverFactory.createItpSolver()),
                    createConcrProd2Lens(),
                    system),
                new CombinedLazyCegarXtaPrecRefiner<>(new ItpRefToExplPrec()),
                PruneStrategy.LAZY,
                logger
            ),
            logger
        );

        return new CombinedLazyCegarXtaCheckerConfig<>(cegarChecker, prec);
    }

    private LazyAnalysis<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>, XtaAction, Prod2Prec<ExplPrec, ZonePrec>>
    createLazyAnalysis(final SolverFactory solverFactory,
                       final PartialOrd<Prod2State<ExplState, ZoneState>> abstrPartialOrd,
                       final InitAbstractor<Prod2State<ExplState, ZoneState>, Prod2State<ExplState, ZoneState>> initAbstractor) {
        final Prod2Analysis<ExplState, ZoneState, XtaAction, ExplPrec, ZonePrec>
            prod2ConcrAnalysis = createConcrAnalysis(solverFactory);
        final XtaAnalysis<Prod2State<ExplState, ZoneState>, Prod2Prec<ExplPrec, ZonePrec>>
            xtaConcrAnalysis = XtaAnalysis.create(system, prod2ConcrAnalysis);

        return LazyAnalysis.create(
            XtaOrd.create(abstrPartialOrd),
            xtaConcrAnalysis.getInitFunc(),
            xtaConcrAnalysis.getTransFunc(),
            XtaInitAbstractor.create(initAbstractor)
        );
    }

    private Prod2Analysis<ExplState, ZoneState, XtaAction, ExplPrec, ZonePrec> createConcrAnalysis(final SolverFactory solverFactory) {
        return Prod2Analysis.create(
            createConcrDataAnalysis(solverFactory),
            createConcrClockAnalysis()
        );
    }

    private Analysis<ExplState, XtaAction, ExplPrec> createConcrDataAnalysis(final SolverFactory solverFactory) {
        return CombinedLazyCegarXtaAnalysis.create(
            ExplStmtAnalysis.create(
                solverFactory.createSolver(),
                system.getInitVal().toExpr()
                ,1
            )
        );
    }

    private Analysis<ZoneState, XtaAction, ZonePrec> createConcrClockAnalysis() {
        return XtaZoneAnalysis.getInstance();
    }

    private LazyStrategy<Prod2State<ExplState, ZoneState>, Prod2State<ExplState, ZoneState>, LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, XtaAction>
    createLazyStrategy(final ClockStrategy clockStrategy) {
        final LazyStrategy<ExplState, ExplState, LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, XtaAction>
            dataLazyStrategy = forceCast(createDataStrategy2());

        final LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, XtaAction>
            clockLazyStrategy = forceCast(createClockStrategy(clockStrategy));

        final Function<LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, ?> projection = s -> Tuple3.of(
            s.getConcrState().getLocs(),
            dataLazyStrategy.getProjection().apply(s),
            clockLazyStrategy.getProjection().apply(s)
        );

        final Lens<LazyState<XtaState<Prod2State<ExplState, ZoneState>>, XtaState<Prod2State<ExplState, ZoneState>>>, Prod2State<ExplState, ZoneState>>
            lens = createConcrProd2Lens();
        return new Prod2LazyStrategy<>(lens, dataLazyStrategy, clockLazyStrategy, projection);
    }

    private LazyStrategy<ExplState, ExplState, LazyState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, XtaAction> createDataStrategy2() {
        return new BasicLazyStrategy<>(
            createDataLens(),
            createDataConcretizer()
        );
    }

    private Lens<LazyState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, ExplState> createDataLens() {
        return LazyXtaLensUtils.createConcrDataLens();
    }

    private Concretizer<ExplState, ExplState> createDataConcretizer() {
        return BasicConcretizer.create(ExplOrd.getInstance());
    }

    private LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction> createClockStrategy(final ClockStrategy clockStrategy) {
        return switch (clockStrategy) {
            case BWITP, FWITP -> createLazyZoneStrategy(clockStrategy);
            case LU -> throw new AssertionError();
        };
    }

    private LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction>
    createLazyZoneStrategy(final ClockStrategy clockStrategy) {

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

    private Prod2Prec<ExplPrec, ZonePrec> createConcrPrec() {
        return Prod2Prec.of(createConcrDataPrec(), createConcrZonePrec());
    }

    private ExplPrec createConcrDataPrec() {
        return ExplPrec.empty();
    }

    private ZonePrec createConcrZonePrec() {
        return ZonePrec.of(system.getClockVars());
    }

}
