package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.AlgorithmStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.BasicAlgorithmStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.BasicConcretizer;
import hu.bme.mit.theta.analysis.algorithm.lazy.Concretizer;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.Prod2Strategy;
import hu.bme.mit.theta.analysis.expl.ExplExprInterpolator;
import hu.bme.mit.theta.analysis.expl.ExplLattice;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.itp.BwItpStrategy;
import hu.bme.mit.theta.analysis.itp.FwItpStrategy;
import hu.bme.mit.theta.analysis.itp.Interpolator;
import hu.bme.mit.theta.analysis.itp.ItpAnalysis;
import hu.bme.mit.theta.analysis.itp.ItpState;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.zone.ZoneInterpolator;
import hu.bme.mit.theta.analysis.zone.ZoneLattice;
import hu.bme.mit.theta.analysis.zone.ZoneOrd;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.xta.analysis.XtaInitAbstractor;
import hu.bme.mit.theta.xta.analysis.XtaOrd;
import hu.bme.mit.theta.xta.analysis.XtaState;
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
    Abstractor<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
    create(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy, final SearchStrategy searchStrategy) {

        final Factory<DConcr, CConcr, DAbstr, CAbstr, DPrec, CPrec>
                factory = new Factory<>(system, dataStrategy, clockStrategy, searchStrategy);
        final Abstractor<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
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

        public final Abstractor<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
        create() {
            final AlgorithmStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>,
                    ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    algorithmStrategy = createAlgorithmStrategy(system, dataStrategy, clockStrategy);

            final PartialOrd<Prod2State<DAbstr, CAbstr>> abstrPartialOrd = algorithmStrategy.getPartialOrd();
            final InitAbstractor<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>> initAbstractor = algorithmStrategy.getInitAbstractor();
            final ItpAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    itpAnalysis = createItpAnalysis(abstrPartialOrd, initAbstractor);

            final Prod2Prec<DPrec, CPrec> prec = createConcrPrec();
            final Abstractor<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction, UnitPrec>
                    abstractor = new LazyXtaAbstractor<>(system, searchStrategy, algorithmStrategy, itpAnalysis, prec);
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

        private ItpAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
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

            final ItpAnalysis<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>, XtaAction, Prod2Prec<DPrec, CPrec>>
                    itpAnalysis = ItpAnalysis.create(xtaAbstrPartialOrd, xtaConcrInitFunc, xtaConcrTransFunc, xtaInitAbstractor);
            return itpAnalysis;
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

        private AlgorithmStrategy<Prod2State<DConcr, CConcr>, Prod2State<DAbstr, CAbstr>, ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
        createAlgorithmStrategy(final XtaSystem system, final DataStrategy dataStrategy, final ClockStrategy clockStrategy){
            final AlgorithmStrategy<DConcr, DAbstr, ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    dataAlgorithmStrategy = createDataStrategy(system, dataStrategy);
            final AlgorithmStrategy<CConcr, CAbstr, ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, XtaAction>
                    clockAlgorithmStrategy = createClockStrategy(system, clockStrategy);
            final Function<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, ?> projection = s -> Tuple3.of(
                    s.getConcrState().getLocs(),
                    dataAlgorithmStrategy.getProjection().apply(s),
                    clockAlgorithmStrategy.getProjection().apply(s));
            final Lens<ItpState<XtaState<Prod2State<DConcr, CConcr>>, XtaState<Prod2State<DAbstr, CAbstr>>>, Prod2State<DConcr, CConcr>>
                    lens = LazyXtaLensUtils.createConcrProd2Lens();
            return new Prod2Strategy<>(lens, dataAlgorithmStrategy, clockAlgorithmStrategy, projection);
        }

        private AlgorithmStrategy createDataStrategy(final XtaSystem system, final DataStrategy dataStrategy){
            switch (dataStrategy) {
                case NONE:
                    final Lens<ItpState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, ExplState>
                            lens = LazyXtaLensUtils.createConcrDataLens();
                    return new BasicAlgorithmStrategy<>(lens);
                case BWITP:
                case FWITP:
                    return createItpExplStrategy(system, dataStrategy);
                default:
                    throw new AssertionError();
            }
        }

        private AlgorithmStrategy<ExplState, ExplState, ItpState<XtaState<Prod2State<ExplState, ?>>, XtaState<Prod2State<ExplState, ?>>>, XtaAction>
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

        private AlgorithmStrategy createClockStrategy(final XtaSystem system, final ClockStrategy clockStrategy){
            switch (clockStrategy) {
                case BWITP:
                case FWITP:
                    return createItpZoneStrategy(system, clockStrategy);
                case LU:
                    final Lens<ItpState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, LuZoneState>>>, LuZoneState>
                            lens = LazyXtaLensUtils.createAbstrClockLens();
                    return new LuZoneStrategy2<>(lens);
                default:
                    throw new AssertionError();
            }
        }

        private AlgorithmStrategy<ZoneState, ZoneState, ItpState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, XtaAction>
        createItpZoneStrategy(final XtaSystem system, final ClockStrategy clockStrategy){

            final Lens<ItpState<XtaState<Prod2State<?, ZoneState>>, XtaState<Prod2State<?, ZoneState>>>, ItpState<ZoneState, ZoneState>>
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
