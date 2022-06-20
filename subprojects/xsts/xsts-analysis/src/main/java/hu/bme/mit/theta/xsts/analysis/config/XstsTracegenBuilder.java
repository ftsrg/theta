package hu.bme.mit.theta.xsts.analysis.config;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.algorithm.tracegen.TraceGenChecker;
import hu.bme.mit.theta.analysis.expl.*;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsAllVarsInitPrec;

import java.util.function.Predicate;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

final public class XstsTracegenBuilder {
    private final SolverFactory solverFactory;
    private Logger logger = NullLogger.getInstance();

    public XstsTracegenBuilder(final SolverFactory solverFactory) {
        this.solverFactory = solverFactory;
    }

    public XstsTracegenBuilder logger(final Logger logger) {
        this.logger = logger;
        return this;
    }

    public XstsTracegenConfig<? extends State, ? extends Action, ? extends Prec> build(final XSTS xsts) {

        final Solver solver1 = solverFactory.createSolver(); // refinement // TODO handle separate solvers in a nicer way
        final Solver solver2 = solverFactory.createSolver(); // abstraction // TODO handle separate solvers in a nicer way

        final XstsAnalysis<ExplState, ExplPrec> analysis = XstsAnalysis.create(ExplStmtAnalysis.create(solver2, True(), 1));
        final LTS<XstsState<ExplState>, XstsAction> lts = XstsLts.create(xsts, XstsStmtOptimizer.create(ExplStmtOptimizer.getInstance()));

        final InitFunc<XstsState<ExplState>, ExplPrec> initFunc = analysis.getInitFunc();
        final TransFunc<XstsState<ExplState>, XstsAction, ExplPrec> transFunc = analysis.getTransFunc();

        final Expr<BoolType> negProp = Not(xsts.getProp());
        final Predicate<XstsState<ExplState>> target = new XstsStatePredicate<ExplStatePredicate, ExplState>(new ExplStatePredicate(negProp, solver2));
        final ArgBuilder<XstsState<ExplState>, XstsAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis, target, true);

        final Abstractor<XstsState<ExplState>, XstsAction, ExplPrec> abstractor = BasicAbstractor.builder(argBuilder)
                .waitlist(PriorityWaitlist.create(XstsConfigBuilder.Search.DFS.comparator))
                .stopCriterion(StopCriterions.fullExploration())
                .logger(logger).build();

        TraceGenChecker<XstsState<ExplState>, XstsAction, ExplPrec> tracegenChecker = TraceGenChecker.create(logger, lts, initFunc, transFunc, solver1, abstractor);
        return XstsTracegenConfig.create(tracegenChecker, new XstsAllVarsInitPrec().createExpl(xsts));
    }
}
