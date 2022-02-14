package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.expl.ExplExprInterpolator;
import hu.bme.mit.theta.analysis.expl.ExplLattice;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.*;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.*;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplAnalysis;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplTransFunc;
import hu.bme.mit.theta.xta.analysis.expr.XtaExprInvTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneInvTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.XtaZoneTransFunc;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

import java.util.function.Function;

@SuppressWarnings({"unchecked", "rawtypes"})
public final class LazyXtaAbstractorFactory {

    public static <DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State, DPrec extends Prec, CPrec extends Prec>
    Abstractor<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
    create(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy, final SearchStrategy searchStrategy) {

        final Factory<DConcr, CConcr, DAbstr, CAbstr, DPrec, CPrec>
                factory = new Factory<>(system, dataStrategy, clockStrategy, searchStrategy);
        final Abstractor<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
                abstractor = factory.create();
        return abstractor;
    }

    private static class Factory<DConcr extends State, CConcr extends State, DAbstr extends State, CAbstr extends State, DPrec extends Prec, CPrec extends Prec> {

        private final XtaSystem system;
        private final DataStrategy dataStrategy;
        private final ClockStrategy clockStrategy;
        private final SearchStrategy searchStrategy;

        public Factory(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy, final SearchStrategy searchStrategy){
            this.system = system;
            this.dataStrategy = dataStrategy;
            this.clockStrategy = clockStrategy;
            this.searchStrategy = searchStrategy;
        }

        public final Abstractor<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
        create() {
            final LazyStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>,
                    LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    lazyStrategy = createAlgorithmStrategy(system, dataStrategy, clockStrategy);

            final PartialOrd<Prod2State<DAbstr, CAbstr>> abstrPartialOrd = lazyStrategy.getPartialOrd();
            final InitAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>> initAbstractor = lazyStrategy.getInitAbstractor();
            final LazyAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    lazyAnalysis = createItpAnalysis(abstrPartialOrd, initAbstractor);

            final Prod2Prec<DPrec, CPrec> prec = createConcrPrec();
            final Abstractor<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
                    abstractor = new LazyXtaAbstractor<>(system, searchStrategy, lazyStrategy, lazyAnalysis, prec);
            return abstractor;
        }

        private Prod2Prec<DPrec, CPrec> createConcrPrec() {
            final Prec dataPrec = createConcrDataPrec();
            final Prec clockPrec = createConcrZonePrec();
            final Prod2Prec prec = Prod2Prec.of(dataPrec, clockPrec);
            return prec;
        }

        private Prec createConcrDataPrec() {
            switch (dataStrategy) {
                case FWITP:
                case BWITP:
                case NONE:
                    return UnitPrec.getInstance();
                default:
                    throw new AssertionError();
            }
        }

        private Prec createConcrZonePrec() {
            switch (clockStrategy) {
                case BWITP:
                case FWITP:
                case LU:
                    return ZonePrec.of(system.getClockVars());
                default:
                    throw new AssertionError();
            }
        }

        private LazyAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
        createItpAnalysis(final PartialOrd<Prod2State<DAbstr, CAbstr>> abstrPartialOrd,
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
            switch (dataStrategy) {
                case FWITP:
                case BWITP:
                case NONE:
                    return XtaExplAnalysis.create(system);
                default:
                    throw new AssertionError();
            }
        }

        private Analysis createConcrClockAnalysis() {
            switch (clockStrategy) {
                case FWITP:
                case BWITP:
                case LU:
                    return XtaZoneAnalysis.getInstance();
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
        createAlgorithmStrategy(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy){
            final LazyStrategy<DConcr, DAbstr, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    dataLazyStrategy = createDataStrategy(system, dataStrategy);
            final LazyStrategy<CConcr, CAbstr, LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    clockLazyStrategy = createClockStrategy(system, clockStrategy);
            final Function<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, ?> projection = s -> Tuple3.of(
                    s.getConcrState().getLocs(),
                    dataLazyStrategy.getProjection().apply(s),
                    clockLazyStrategy.getProjection().apply(s));
            final Lens<LazyState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
                    lens = LazyXtaLensUtils.createConcrProd2Lens();
            return new Prod2LazyStrategy<>(lens, dataLazyStrategy, clockLazyStrategy, projection);
        }

        private LazyStrategy createDataStrategy(final XtaSystem system, final DataStrategy dataStrategy){
            switch (dataStrategy) {
                case NONE:
                    final Lens<LazyState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, ExplState>
                            lens = LazyXtaLensUtils.createConcrDataLens();
                    return new BasicLazyStrategy<>(lens);
                case BWITP:
                case FWITP:
                    return createItpExplStrategy(system, dataStrategy);
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<ExplState, ExplState, LazyState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, XtaAction>
        createItpExplStrategy(final XtaSystem system, final DataStrategy dataStrategy){

            final Lattice<ExplState> lattice = ExplLattice.getInstance();
            final Interpolator<ExplState, BasicExprState> interpolator = ExplExprInterpolator.getInstance();
            final Concretizer<ExplState, ExplState> concretizer = BasicConcretizer.create(ExplOrd.getInstance());
            final InvTransFunc<BasicExprState, XtaAction, UnitPrec> exprInvTransFunc = XtaExprInvTransFunc.getInstance();
            final UnitPrec prec = UnitPrec.getInstance();

            switch (dataStrategy){
                case BWITP:
                    return new BwItpStrategy<>(LazyXtaLensUtils.createItpDataLens(), lattice, interpolator, concretizer, exprInvTransFunc, prec);
                case FWITP:
                    final TransFunc<ExplState, XtaAction, UnitPrec> explTransFunc = XtaExplTransFunc.create(system);
                    return new FwItpStrategy<>(LazyXtaLensUtils.createItpDataLens(), lattice, interpolator, concretizer, exprInvTransFunc, prec, explTransFunc, prec);
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy createClockStrategy(final XtaSystem system, final ClockStrategy clockStrategy){
            switch (clockStrategy) {
                case BWITP:
                case FWITP:
                    return createItpZoneStrategy(system, clockStrategy);
                case LU:
                    final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, LuZoneState>>>, LuZoneState>
                            lens = LazyXtaLensUtils.createAbstrClockLens();
                    return new LuZoneStrategy2<>(lens);
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<ZoneState, ZoneState, LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction>
        createItpZoneStrategy(final XtaSystem system, final ClockStrategy clockStrategy){

            final Lens<LazyState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, LazyState<ZoneState, ZoneState>>
                    lens = LazyXtaLensUtils.createItpClockLens();
            final Lattice<ZoneState> lattice = ZoneLattice.getInstance();
            final Interpolator<ZoneState, ZoneState> interpolator = ZoneInterpolator.getInstance();
            final Concretizer<ZoneState, ZoneState> concretizer = BasicConcretizer.create(ZoneOrd.getInstance());
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
    }
}
