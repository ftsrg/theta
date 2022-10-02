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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.*;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsAllVarsInitPrec;
import hu.bme.mit.theta.xsts.analysis.initprec.XstsVarListInitPrec;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.*;
import java.util.function.Predicate;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

final public class XstsTracegenBuilder {
    private final SolverFactory solverFactory;
    private final boolean transitionCoverage;
    private Logger logger = NullLogger.getInstance();
    private boolean getFullTraces = false;
    private File varFile = null;

    public XstsTracegenBuilder(final SolverFactory solverFactory, boolean transitionCoverage) {
        this.solverFactory = solverFactory;
        this.transitionCoverage = transitionCoverage;
    }

    public XstsTracegenBuilder logger(final Logger logger) {
        this.logger = logger;
        return this;
    }

    public XstsTracegenBuilder setGetFullTraces(boolean getFullTraces) {
        this.getFullTraces = getFullTraces;
        return this;
    }

    public XstsTracegenBuilder setVarFile(String filename) {
        if(filename!=null) {
            this.varFile = new File(filename);
        }
        return this;
    }

    public XstsTracegenConfig<? extends State, ? extends Action, ? extends Prec> build(final XSTS xsts) {
        final Solver solver2 = solverFactory.createSolver(); // abstraction // TODO handle separate solvers in a nicer way

        final XstsAnalysis<ExplState, ExplPrec> analysis = XstsAnalysis.create(ExplAnalysis.create(solver2, True()));
        final LTS<XstsState<ExplState>, XstsAction> lts = XstsLts.create(xsts, XstsStmtOptimizer.create(ExplStmtOptimizer.getInstance()));

        final Expr<BoolType> negProp = Not(xsts.getProp());
        final Predicate<XstsState<ExplState>> target = new XstsStatePredicate<ExplStatePredicate, ExplState>(new ExplStatePredicate(negProp, solver2));
        final ArgBuilder<XstsState<ExplState>, XstsAction, ExplPrec> argBuilder = ArgBuilder.create(lts, analysis, target, true);

        final Abstractor<XstsState<ExplState>, XstsAction, ExplPrec> abstractor = BasicAbstractor.builder(argBuilder)
                .waitlist(PriorityWaitlist.create(XstsConfigBuilder.Search.DFS.comparator))
                .stopCriterion(StopCriterions.fullExploration())
                .logger(logger).build();

        TraceGenChecker<XstsState<ExplState>, XstsAction, ExplPrec> tracegenChecker = TraceGenChecker.create(logger, abstractor, getFullTraces);

        if(varFile==null) {
            return XstsTracegenConfig.create(tracegenChecker, new XstsAllVarsInitPrec().createExpl(xsts));
        } else {
            try(Scanner scanner = new Scanner(varFile)) {
                Set<String> varNamesToAdd = new HashSet<>();
                Set<VarDecl<?>> varsToAdd = new HashSet<>();
                while(scanner.hasNext()) {
                    varNamesToAdd.add(scanner.nextLine().trim());
                }
                Collection<VarDecl<?>> vars = xsts.getVars();
                for (VarDecl<?> var : vars) {
                    if(varNamesToAdd.contains(var.getName())) {
                        varsToAdd.add(var);
                    }
                }
                checkState(varNamesToAdd.size()==varsToAdd.size());
                return XstsTracegenConfig.create(tracegenChecker, new XstsVarListInitPrec(varsToAdd).setTransitionCoverage(transitionCoverage).createExpl(xsts));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
