package hu.bme.mit.theta.analysis.algorithm.tracegen;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.*;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;
import hu.bme.mit.theta.analysis.algorithm.cegar.BasicAbstractor;
import hu.bme.mit.theta.analysis.algorithm.cegar.abstractor.StopCriterions;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

public class TraceGenChecker <S extends ExprState, A extends StmtAction, P extends Prec> implements SafetyChecker<S, A, P> {
    private final Logger logger;
    private final LTS<S, A> lts;
    private final InitFunc<S, P> initFunc;
    private final TransFunc<S, A, P> transFunc;
    private final Solver solver;
    private final Abstractor<S, A, P> abstractor;

    private TraceGenChecker(final Logger logger,
                            final LTS<S, A> lts,
                            final InitFunc<S, P> initFunc,
                            final TransFunc<S, A, P> transFunc,
                            final Solver solver,
                            final Abstractor<S, A, P> abstractor) {

        this.logger = logger;
        this.lts = lts;
        this.initFunc = initFunc;
        this.transFunc = transFunc;
        this.solver = solver;
        this.abstractor = abstractor;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> TraceGenChecker<S,A,P> create(final Logger logger,
                                                                                                     final LTS<S, A> lts,
                                                                                                     final InitFunc<S, P> initFunc,
                                                                                                     final TransFunc<S, A, P> transFunc,
                                                                                                     final Solver solver,
                                                                                                     final Abstractor<S,A,P> abstractor) {
        return new TraceGenChecker<S,A,P>(logger, lts, initFunc, transFunc, solver, abstractor);
    }

    private List<Trace<S,A>> traces = new ArrayList<>();

    public List<Trace<S, A>> getTraces() {
        return traces;
    }

    @Override
    public SafetyResult<S, A> check(P prec) {
        final ARG<S, A> arg = abstractor.createArg();
        AbstractorResult abstractorResult = abstractor.check(arg, prec);
        // Stream<ArgTrace<S, A>> cexs = arg.getCexs();
        traces = arg.getNodes().map(ArgTrace::to).map(ArgTrace::toTrace).toList();
        // traces = cexs.map(ArgTrace::toTrace).toList();
        /*
        for (Trace<S, A> trace : this.traces) {
            logger.write(Logger.Level.SUBSTEP, "%s%n", trace);
            logger.write(Logger.Level.SUBSTEP, "---------------------------%n");
        }
        */

        /*
        logger.write(Logger.Level.INFO, "Configuration: %s%n", this);
        generateTraces(prec); // generates traces and puts them into the member list traces
        for (Trace<S, A> trace : this.traces) {
            logger.write(Logger.Level.SUBSTEP, "%s%n", trace);
            logger.write(Logger.Level.SUBSTEP, "---------------------------%n");
        }
         */

        return SafetyResult.unsafe(this.traces.get(0), ARG.create((state1, state2) -> false)); // TODO: this is only a placeholder
    }
/*
    private void generateTraces(P prec) {
        final Collection<? extends S> initStates = initFunc.getInitStates(prec);
        traces.clear();
        logger.write(Logger.Level.MAINSTEP, "Generating traces...%n");

        for (S initState : initStates) {
            logger.write(Logger.Level.SUBSTEP, "Starting traces from:%n\"%s\"%n", initState);
            final Deque<S> states = new ArrayDeque<>();
            states.push(initState);
            final Deque<A> actions = new ArrayDeque<>();
            step(prec, states, actions);
        }

        logger.write(Logger.Level.MAINSTEP, "Generating traces done, generated %d traces%n", traces.size());
    }

    public boolean feasibilityCheck(Trace<S,A> trace, final Solver solver) {
        solver.push();
        StmtAction stmtAction = new StmtAction() {
            @Override
            public List<Stmt> getStmts() {
                return trace.getActions().stream()
                        .map(a -> a.getStmts()
                        .stream())
                        .reduce(Streams::concat)
                        .map(s -> s.collect(Collectors.toList()))
                        .orElse(List.of());
            }
        };
        solver.add(PathUtils.unfold(stmtAction.toExpr(), indexing(0)));
        if (solver.check().isUnsat()) {
            solver.pop();
            return false;
        }
        solver.pop();
        return true;
    }

    private boolean step(P prec, Deque<S> states, Deque<A> actions) {
        // bound
        if(states.size()>8) {
            return false;
        }
        boolean foundOne = false;
        S state = states.peek();

        final Collection<A> enabledActions = lts.getEnabledActionsFor(state);
        if(enabledActions.isEmpty()) {
            logger.write(Logger.Level.INFO, "Generated next trace%n");
            Trace<S, A> t = Trace.of(states.stream().toList(), actions.stream().toList());
            logger.write(Logger.Level.DETAIL, "Checking feasibility of trace:%n\"%s\"%n",t);
            if(feasibilityCheck(t, solver)) {
                traces.add(t);
                foundOne = true; // trace was feasible (added to list)
            }
        } else {
            for(A a : enabledActions) {
                actions.push(a);
                Collection<? extends S> succStates = transFunc.getSuccStates(state, a, prec);
                for (Iterator<? extends S> i = succStates.iterator(); i.hasNext(); ) {
                    S succState = i.next();
                    if(a != lastlastAction || succState != states.peek()) { // so we do not get stuck infinitely // todo + follow each var explicitly
                        states.push(succState);
                        Trace<S, A> t = Trace.of(states.stream().toList(), actions.stream().toList());
                        logger.write(Logger.Level.DETAIL, "Checking feasibility of partial trace...%n");
                        if(feasibilityCheck(t, solver)) {
                            if(!step(prec, states, actions)) {
                                if(!i.hasNext()) {
                                    traces.add(t);
                                    foundOne = true;
                                }
                            }
                        }
                    }
                    states.pop();
                }
                actions.pop();
            }
        }
        return foundOne;
    }
     */

    @Override
    public String toString() {
        // TODO
        return super.toString();
    }
}
