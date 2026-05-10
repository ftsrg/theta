package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.arg.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.expl.LazyExplAnalysis;
import hu.bme.mit.theta.analysis.algorithm.lazy.expl.LazyExplTransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.LazyExprInvTransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.LazyExprTransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.lu.LuZoneStrategy;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.*;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.*;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;
import hu.bme.mit.theta.xta.analysis.expr.XtaExprPost;
import hu.bme.mit.theta.xta.analysis.expr.XtaExprAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneInvTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneTransFunc;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;

import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.xta.analysis.lazy.LazyXtaLensUtils.createConcrProd2Lens;

@SuppressWarnings({"unchecked", "rawtypes"})
public final class LazyXtaCheckerConfigFactory {

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State, DPrec extends Prec, CPrec extends Prec>
    LazyXtaCheckerConfig<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, Prod2Prec<DPrec, CPrec>>
    create(final XtaSystem system, final Logger logger,
           final DataStrategy dataStrategy, final ClockStrategy clockStrategy,
           final SearchStrategy searchStrategy, final ExprLattice.MeetImpl meetImpl) {
        final Factory<DConcr, CConcr, DAbstr, CAbstr, DPrec, CPrec> factory =
            new Factory<>(system, logger, dataStrategy, clockStrategy, searchStrategy, meetImpl);
        return factory.create();
    }

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State, DPrec extends Prec, CPrec extends Prec>
    LazyXtaCheckerConfig<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, Prod2Prec<DPrec, CPrec>>
    create(final XtaSystem system, final Logger logger,
           final DataStrategy dataStrategy, final ClockStrategy clockStrategy,
           final SearchStrategy searchStrategy) {
        return create(system, logger, dataStrategy, clockStrategy, searchStrategy, ExprLattice.MeetImpl.BASIC);
    }

    private static class Factory<DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State, DPrec extends Prec, CPrec extends Prec> {

        private final XtaSystem system;
        private final Logger logger;
        private final DataStrategy dataStrategy;
        private final ClockStrategy clockStrategy;
        private final SearchStrategy searchStrategy;
        private final ExprLattice.MeetImpl exprMeetImpl;
        private final SolverFactory solverFactory;

        public Factory(final XtaSystem system, final Logger logger,
                       final DataStrategy dataStrategy, final ClockStrategy clockStrategy,
                       final SearchStrategy searchStrategy, final ExprLattice.MeetImpl exprMeetImpl) {
            this.system = system;
            this.logger = logger;
            this.dataStrategy = dataStrategy;
            this.clockStrategy = clockStrategy;
            this.searchStrategy = searchStrategy;
            this.exprMeetImpl = exprMeetImpl;
            solverFactory = Z3LegacySolverFactory.getInstance();
        }

        public final LazyXtaCheckerConfig<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, Prod2Prec<DPrec, CPrec>> create() {
            final LazyStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>,
                    LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    lazyStrategy = createLazyStrategy(system, dataStrategy, clockStrategy);

            final PartialOrd<Prod2State<DAbstr, CAbstr>> abstrPartialOrd = lazyStrategy.getPartialOrd();
            final InitAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>> initAbstractor = lazyStrategy.getInitAbstractor();
            final LazyAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    lazyAnalysis = createLazyAnalysis(abstrPartialOrd, initAbstractor);

            final Prod2Prec<DPrec, CPrec> prec = createConcrPrec();
            final LazyAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    lazyAbstractor = new LazyAbstractor(
                    XtaLts.create(system),
                    searchStrategy,
                    lazyStrategy,
                    lazyAnalysis,
                    s -> ((XtaState) s).isError(),
                    createConcrProd2Lens(),
                    logger
            );
            final LazyChecker<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                  lazyChecker = LazyChecker.create(lazyAbstractor);
            return new LazyXtaCheckerConfig<>(lazyChecker, prec);
        }

        private Prod2Prec<DPrec, CPrec> createConcrPrec() {
            final Prec dataPrec = createConcrDataPrec();
            final Prec clockPrec = createConcrZonePrec();
            final Prod2Prec prec = Prod2Prec.of(dataPrec, clockPrec);
            return prec;
        }

        private Prec createConcrDataPrec() {
            switch (dataStrategy.getConcrDom()) {
                case EXPL:
                case EXPR:
                    return UnitPrec.getInstance();
                default:
                    throw new AssertionError();
            }
        }

        private Prec createConcrZonePrec() {
            switch (clockStrategy) {
                case BW_ITP:
                case FW_ITP:
                case LU:
                    return ZonePrec.of(system.getClockVars());
                default:
                    throw new AssertionError();
            }
        }

        private LazyAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
        createLazyAnalysis(final PartialOrd<Prod2State<DAbstr, CAbstr>> abstrPartialOrd,
                           final InitAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>> initAbstractor) {

            final XtaOrd<Prod2State<DAbstr, CAbstr>> xtaAbstrPartialOrd = XtaOrd.create(abstrPartialOrd);

            final Prod2Analysis<DConcr, CConcr, XtaAction, DPrec, CPrec> prod2ConcrAnalysis = createConcrAnalysis();
            final XtaAnalysis<Prod2State<DConcr, CConcr>, Prod2Prec<DPrec, CPrec>> xtaConcrAnalysis
                    = XtaAnalysis.create(system, prod2ConcrAnalysis);
            final InitFunc<XtaState<Prod2State<DConcr, CConcr>>, Prod2Prec<DPrec, CPrec>> xtaConcrInitFunc
                    = xtaConcrAnalysis.getInitFunc();
            final TransFunc<XtaState<Prod2State<DConcr, CConcr>>, XtaAction, Prod2Prec<DPrec, CPrec>> xtaConcrTransFunc
                    = xtaConcrAnalysis.getTransFunc();

            final XtaInitAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>> xtaInitAbstractor
                    = XtaInitAbstractor.create(initAbstractor);

            final LazyAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    lazyAnalysis = LazyAnalysis.create(xtaAbstrPartialOrd, xtaConcrInitFunc, xtaConcrTransFunc, xtaInitAbstractor);
            return lazyAnalysis;
        }

        private Prod2Analysis<DConcr, CConcr, XtaAction, DPrec, CPrec> createConcrAnalysis() {
            final Analysis<DConcr, XtaAction, DPrec> dataAnalysis = createConcrDataAnalysis();
            final Analysis<CConcr, XtaAction, CPrec> clockAnalysis = createConcrClockAnalysis();
            final Prod2Analysis<DConcr, CConcr, XtaAction, DPrec, CPrec>
                    prod2Analysis = Prod2Analysis.create(dataAnalysis, clockAnalysis);
            return prod2Analysis;
        }

        private Analysis createConcrDataAnalysis() {
            switch (dataStrategy.getConcrDom()) {
                case EXPL:
                    return LazyExplAnalysis.create(system.getInitVal(), XtaExplUtils::post);
                case EXPR:
                    final Solver solver = solverFactory.createSolver();
                    return XtaExprAnalysis.create(system, solver);
                default:
                    throw new AssertionError();
            }
        }

        private Analysis createConcrClockAnalysis() {
            switch (clockStrategy) {
                case FW_ITP:
                case BW_ITP:
                case LU:
                    return XtaZoneAnalysis.create(system.getInitLocs());
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
        createLazyStrategy(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy) {
            final LazyStrategy<DConcr, DAbstr, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    dataLazyStrategy = createDataStrategy2(system, dataStrategy);
            final LazyStrategy<CConcr, CAbstr, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    clockLazyStrategy = createClockStrategy(system, clockStrategy);
            final Function<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, ?> projection = s -> Tuple3.of(
                    s.getConcrState().getLocs(),
                    dataLazyStrategy.getProjection().apply(s),
                    clockLazyStrategy.getProjection().apply(s));
            final Lens<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
                    lens = createConcrProd2Lens();
            return new Prod2LazyStrategy<>(lens, dataLazyStrategy, clockLazyStrategy, projection);
        }

        private LazyStrategy createDataStrategy2(final XtaSystem system, final DataStrategy dataStrategy) {
            final DataStrategy.ConcrDom concrDom = dataStrategy.getConcrDom();
            final DataStrategy.AbstrDom abstrDom = dataStrategy.getAbstrDom();
            final DataStrategy.ItpStrategy itpStrategy = dataStrategy.getItpStrategy();

            final Lens lens = createDataLens(abstrDom);
            final Concretizer concretizer = createDataConcretizer(concrDom, abstrDom);
            if (itpStrategy == DataStrategy.ItpStrategy.NONE) {
                return new IdentityAbstractionLazyStrategy<>(lens, concretizer);
            }
            final Lattice abstrLattice = createDataLattice(abstrDom);
            if (itpStrategy == DataStrategy.ItpStrategy.SEQ) {
                final Function<XtaAction, XtaDataAction> actionTransform = XtaDataAction::of;
                final Solver solver = solverFactory.createSolver();
                final ItpSolver itpSolver = solverFactory.createItpSolver();
                final ExprTraceChecker<ItpRefutation> traceChecker = ExprTraceSeqItpChecker.create(True(), True(), itpSolver);
                return new ExprSeqItpStrategy(lens, actionTransform, abstrLattice, concretizer, solver, traceChecker);
            }
            final Interpolator interpolator = createDataInterpolator(abstrDom);
            final InvTransFunc invTransFunc = createDataInvTransFunc();
            final UnitPrec prec = UnitPrec.getInstance();
            if (itpStrategy == DataStrategy.ItpStrategy.BIN_BW) {
                return new BwItpStrategy(lens, abstrLattice, interpolator, concretizer, invTransFunc, prec);
            }
            final TransFunc abstrTransFunc = createDataAbstrTransFunc(abstrDom);
            if (itpStrategy == DataStrategy.ItpStrategy.BIN_FW) {
                return new FwItpStrategy(lens, abstrLattice, interpolator, concretizer, invTransFunc, prec, abstrTransFunc, prec);
            }
            throw new AssertionError();
        }

        private Lens createDataLens(final DataStrategy.AbstrDom abstrDom) {
            if (abstrDom == DataStrategy.AbstrDom.NONE) {
                return LazyXtaLensUtils.createConcrDataLens();
            }
            return LazyXtaLensUtils.createLazyDataLens();
        }

        private Concretizer createDataConcretizer(final DataStrategy.ConcrDom concrDom, final DataStrategy.AbstrDom abstrDom) {
            final Solver solver;
            switch (concrDom) {
                case EXPL:
                    switch (abstrDom) {
                        case NONE:
                        case EXPL:
                            final PartialOrd<ExplState> partialOrd = ExplOrd.getInstance();
                            return BasicConcretizer.create(partialOrd);
                        case EXPR:
                            solver = solverFactory.createSolver();
                            return ExplExprConcretizer.create(solver);
                    }
                case EXPR:
                    if (abstrDom == DataStrategy.AbstrDom.EXPR) {
                        solver = solverFactory.createSolver();
                        return IndexedExprConcretizer.create(solver);
                    }
                    throw new AssertionError();
                default:
                    throw new AssertionError();
            }
        }

        private Lattice createDataLattice(final DataStrategy.AbstrDom abstrDom) {
            switch (abstrDom) {
                case EXPL:
                    return ExplLattice.getInstance();
                case EXPR:
                    final Solver solver = solverFactory.createSolver();
                    return ExprLattice.create(solver, exprMeetImpl);
                default:
                    throw new AssertionError();
            }
        }

        private Interpolator createDataInterpolator(final DataStrategy.AbstrDom abstrDom) {
            switch (abstrDom) {
                case EXPL:
                    return ExplExprInterpolator.getInstance();
                case EXPR:
                    final Solver solver = solverFactory.createSolver();
                    final ItpSolver itpSolver = solverFactory.createItpSolver();
                    return ExprInterpolator.create(solver, itpSolver);
                default:
                    throw new AssertionError();
            }
        }

        private InvTransFunc createDataInvTransFunc() {
            return LazyExprInvTransFunc.create(XtaExplUtils::pre);
        }

        private TransFunc createDataAbstrTransFunc(final DataStrategy.AbstrDom abstrDom) {
            switch (abstrDom) {
                case EXPL:
                    return LazyExplTransFunc.create(XtaExplUtils::post);
                case EXPR:
                    return LazyExprTransFunc.create(XtaExprPost.create());
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy createClockStrategy(final XtaSystem system, final ClockStrategy clockStrategy) {
            switch (clockStrategy) {
                case BW_ITP:
                case FW_ITP:
                    return createLazyZoneStrategy(system, clockStrategy);
                case LU:
                    final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, LuZoneState>>>, LuZoneState>
                            lens = LazyXtaLensUtils.createAbstrClockLens();
                    return new LuZoneStrategy<>(lens, XtaLuZoneUtils::pre);
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction>
        createLazyZoneStrategy(final XtaSystem system, final ClockStrategy clockStrategy) {

            final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, LazyState<ZoneState, ZoneState>>
                    lens = LazyXtaLensUtils.createLazyClockLens();
            final Lattice<ZoneState> lattice = ZoneLattice.getInstance();
            final Interpolator<ZoneState, ZoneState> interpolator = ZoneInterpolator.getInstance();
            final PartialOrd<ZoneState> partialOrd = ZoneOrd.getInstance();
            final Concretizer<ZoneState, ZoneState> concretizer = BasicConcretizer.create(partialOrd);
            final InvTransFunc<ZoneState, XtaAction, ZonePrec> zoneInvTransFunc = XtaZoneInvTransFunc.getInstance();
            final ZonePrec prec = ZonePrec.of(system.getClockVars());

            switch (clockStrategy){
                case BW_ITP:
                    return new BwItpStrategy<>(lens, lattice, interpolator, concretizer, zoneInvTransFunc, prec);
                case FW_ITP:
                    final TransFunc<ZoneState, XtaAction, ZonePrec> zoneTransFunc = XtaZoneTransFunc.getInstance();
                    return new FwItpStrategy<>(lens, lattice, interpolator, concretizer, zoneInvTransFunc, prec, zoneTransFunc, prec);
                default:
                    throw new AssertionError();
            }
        }
    }
}
