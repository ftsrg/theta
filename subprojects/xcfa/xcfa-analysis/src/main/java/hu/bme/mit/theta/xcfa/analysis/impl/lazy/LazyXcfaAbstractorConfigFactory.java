package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.*;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.*;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.expr.*;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyAbstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.expl.ExplAnalysis;
import hu.bme.mit.theta.analysis.algorithm.lazy.expl.ExplTransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprAnalysis;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprInvTransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprTransFunc;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAnalysis;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaPrec;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.impl.singlethread.*;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.xcfa.analysis.impl.lazy.XcfaLensUtils.createConcrDataLens;

@SuppressWarnings({"unchecked", "rawtypes"})
public class LazyXcfaAbstractorConfigFactory {
    public static <DConcr extends ExprState, DAbstr extends ExprState, A extends XcfaAction, DPrec extends Prec>
    LazyXcfaAbstractorConfig<DConcr, DAbstr, A, DPrec>
    create(final XCFA program, final DataStrategy2 dataStrategy, final SearchStrategy searchStrategy, final ExprMeetStrategy meetStrategy) {

        final Factory<DConcr, DAbstr, A, DPrec>
                factory = new Factory<>(program, dataStrategy, searchStrategy, meetStrategy);
        return factory.create();
    }

    public static <DConcr extends ExprState, DAbstr extends ExprState, A extends XcfaAction, DPrec extends Prec>
    LazyXcfaAbstractorConfig<DConcr, DAbstr, A, DPrec>
    create(final XCFA program, final DataStrategy2 dataStrategy, final SearchStrategy searchStrategy) {
        return create(program, dataStrategy, searchStrategy, ExprMeetStrategy.BASIC);
    }

    private static class Factory<DConcr extends ExprState, DAbstr extends ExprState, A extends XcfaAction, DPrec extends Prec> {

        private final XCFA program;
        private final DataStrategy2 dataStrategy;
        private final SearchStrategy searchStrategy;
        private final ExprMeetStrategy meetStrategy;
        private final SolverFactory solverFactory;

        public Factory(final XCFA program, final DataStrategy2 dataStrategy,
                       final SearchStrategy searchStrategy, final ExprMeetStrategy meetStrategy){
            this.program = program;
            this.dataStrategy = dataStrategy;
            this.searchStrategy = searchStrategy;
            this.meetStrategy = meetStrategy;
            solverFactory = Z3SolverFactory.getInstance();
        }

        public final LazyXcfaAbstractorConfig<DConcr, DAbstr, A, DPrec> create() {
            final LazyStrategy<DConcr, DAbstr,
                                LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, A>
                    lazyStrategy = createLazyStrategy(program, dataStrategy);

            final PartialOrd<DAbstr> abstrPartialOrd = lazyStrategy.getPartialOrd();
            final InitAbstractor<DConcr, DAbstr> initAbstractor = lazyStrategy.getInitAbstractor();
            final LazyAnalysis<XcfaState<DConcr>, XcfaState<DAbstr>, A, XcfaPrec<DPrec>>
                    lazyAnalysis = createLazyAnalysis(abstrPartialOrd, initAbstractor);

            final XcfaPrec<DPrec> prec = XcfaPrec.create(createConcrPrec());
            final Abstractor<LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, A, XcfaPrec<DPrec>>
                    abstractor = new LazyAbstractor(
                    new XcfaSTLts(),
                    searchStrategy,
                    lazyStrategy,
                    lazyAnalysis,
                    s -> ((XcfaSTState) s).isError(),
                    createConcrDataLens()
            );
            return new LazyXcfaAbstractorConfig<>(abstractor, prec);
        }

        private DPrec createConcrPrec() {
            return createConcrDataPrec();
        }

        private DPrec createConcrDataPrec() {
            switch (dataStrategy.getConcrDom()) {
                case EXPL:
                case EXPR:
                    return (DPrec) UnitPrec.getInstance();
                default:
                    throw new AssertionError();
            }
        }

        private LazyAnalysis<XcfaState<DConcr>, XcfaState<DAbstr>, A, XcfaPrec<DPrec>>
        createLazyAnalysis(final PartialOrd<DAbstr> abstrPartialOrd,
                           final InitAbstractor<DConcr, DAbstr> initAbstractor) {

            final XcfaSTOrd<DAbstr> xcfaAbstrPartialOrd = XcfaSTOrd.create(abstrPartialOrd);

            final Analysis<DConcr, A, DPrec> concrAnalysis = createConcrAnalysis();
            final XcfaAnalysis<DConcr, A, DPrec> xcfaConcrAnalysis
                    = XcfaAnalysis.create(
                            List.of(program.getMainProcess().getMainProcedure().getInitLoc()),
                            XcfaSTOrd.create(concrAnalysis.getPartialOrd()),
                            XcfaSTInitFunc.create(program.getMainProcess().getMainProcedure().getInitLoc(), concrAnalysis.getInitFunc()),
                            XcfaSTTransFunc.create(concrAnalysis.getTransFunc())
                    );
            final InitFunc<XcfaState<DConcr>, XcfaPrec<DPrec>> xcfaConcrInitFunc
                    = xcfaConcrAnalysis.getInitFunc();
            final TransFunc<XcfaState<DConcr>, A, XcfaPrec<DPrec>> xcfaConcrTransFunc
                    = xcfaConcrAnalysis.getTransFunc();

            final XcfaInitAbstractor<DConcr, DAbstr> xcfaInitAbstractor
                    = XcfaInitAbstractor.create(initAbstractor, XcfaSTState::create);

            final LazyAnalysis<XcfaState<DConcr>, XcfaState<DAbstr>, A, XcfaPrec<DPrec>>
                    lazyAnalysis = LazyAnalysis.create(xcfaAbstrPartialOrd, xcfaConcrInitFunc, xcfaConcrTransFunc, xcfaInitAbstractor);
            return lazyAnalysis;
        }

        private Analysis<DConcr, A, DPrec> createConcrAnalysis() {
            return createConcrDataAnalysis();
        }

        private Analysis createConcrDataAnalysis() {
            final MutableValuation mutVal = new MutableValuation();
            XcfaUtils.getVars(program).forEach(varDecl -> mutVal.put(varDecl, TypeUtils.getDefaultValue(varDecl.getType())));

            switch (dataStrategy.getConcrDom()) {
                case EXPL:
                    return ExplAnalysis.create(mutVal, XcfaExplActionPost.create());
                case EXPR:
                    final Solver solver = solverFactory.createSolver();
                    return ExprAnalysis.create(mutVal, solver);
                default:
                    throw new AssertionError();
            }
        }

        private LazyStrategy<DConcr, DAbstr, LazyState<XcfaState<DConcr>, XcfaState<DAbstr>>, A>
        createLazyStrategy(final XCFA program, final DataStrategy2 dataStrategy) {
            return new XcfaLazyStrategy(createDataStrategy2(program, dataStrategy));
        }

        private LazyStrategy createDataStrategy2(final XCFA program, final DataStrategy2 dataStrategy) {
            final DataStrategy2.ConcrDom concrDom = dataStrategy.getConcrDom();
            final DataStrategy2.AbstrDom abstrDom = dataStrategy.getAbstrDom();
            final DataStrategy2.ItpStrategy itpStrategy = dataStrategy.getItpStrategy();

            final Lens lens = createDataLens(abstrDom);
            final Concretizer concretizer = createDataConcretizer(concrDom, abstrDom);
            if (itpStrategy == DataStrategy2.ItpStrategy.NONE) {
                return new IdentityAbstractionLazyStrategy<>(lens, concretizer);
            }
            final Lattice abstrLattice = createDataLattice(abstrDom);
            if (itpStrategy == DataStrategy2.ItpStrategy.SEQ) {
                final Solver solver = solverFactory.createSolver();
                final ItpSolver itpSolver = solverFactory.createItpSolver();
                final ExprTraceChecker<ItpRefutation> traceChecker = ExprTraceSeqItpChecker.create(True(), True(), itpSolver);
                return new ExprSeqItpStrategy(lens, s -> s, abstrLattice, concretizer, solver, traceChecker);
            }
            final Interpolator interpolator = createDataInterpolator(abstrDom);
            final InvTransFunc invTransFunc = createDataInvTransFunc();
            final UnitPrec prec = UnitPrec.getInstance();
            if (itpStrategy == DataStrategy2.ItpStrategy.BIN_BW) {
                return new BwItpStrategy(lens, abstrLattice, interpolator, concretizer, invTransFunc, prec);
            }
            final TransFunc abstrTransFunc = createDataAbstrTransFunc(abstrDom);
            if (itpStrategy == DataStrategy2.ItpStrategy.BIN_FW) {
                return new FwItpStrategy(lens, abstrLattice, interpolator, concretizer, invTransFunc, prec, abstrTransFunc, prec);
            }
            throw new AssertionError();
        }

        private Lens createDataLens(final DataStrategy2.AbstrDom abstrDom) {
            if (abstrDom == DataStrategy2.AbstrDom.NONE) {
                return createConcrDataLens();
            }
            return XcfaLensUtils.createLazyDataLens();
        }

        private Concretizer createDataConcretizer(final DataStrategy2.ConcrDom concrDom, final DataStrategy2.AbstrDom abstrDom) {
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
                    if (abstrDom == DataStrategy2.AbstrDom.EXPR) {
                        solver = solverFactory.createSolver();
                        return IndexedExprConcretizer.create(solver);
                    }
                    throw new AssertionError();
                default:
                    throw new AssertionError();
            }
        }

        private Lattice createDataLattice(final DataStrategy2.AbstrDom abstrDom) {
            switch (abstrDom) {
                case EXPL:
                    return ExplLattice.getInstance();
                case EXPR:
                    final Solver solver = solverFactory.createSolver();
                    switch (meetStrategy) {
                        case BASIC:
                            return ExprLattice.create(solver, BasicExprMeetStrategy.getInstance());
                        case SYNTACTIC:
                            return ExprLattice.create(solver, SyntacticExprMeetStrategy.getInstance());
                        case SEMANTIC:
                            return ExprLattice.create(solver, SemanticExprMeetStrategy.create(solver));
                    }
                default:
                    throw new AssertionError();
            }
        }

        private Interpolator createDataInterpolator(final DataStrategy2.AbstrDom abstrDom) {
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
            return ExprInvTransFunc.create(XcfaExprActionPre.create());
        }

        private TransFunc createDataAbstrTransFunc(final DataStrategy2.AbstrDom abstrDom) {
            switch (abstrDom) {
                case EXPL:
                    return ExplTransFunc.create(XcfaExplActionPost.create());
                case EXPR:
                    return ExprTransFunc.create(XcfaExprActionPost.create());
                default:
                    throw new AssertionError();
            }
        }

    }

}
