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
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

public class TraceGenChecker <S extends ExprState, A extends StmtAction, P extends Prec> implements SafetyChecker<S, A, P> {
    private final Logger logger;
    private final Abstractor<S, A, P> abstractor;

    private TraceGenChecker(final Logger logger,
                            final Abstractor<S, A, P> abstractor) {

        this.logger = logger;
        this.abstractor = abstractor;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> TraceGenChecker<S,A,P> create(final Logger logger,
                                                                                                     final Abstractor<S,A,P> abstractor) {
        return new TraceGenChecker<S,A,P>(logger, abstractor);
    }

    private List<Trace<S,A>> traces = new ArrayList<>();

    public List<Trace<S, A>> getTraces() {
        return traces;
    }

    @Override
    public SafetyResult<S, A> check(P prec) {
        final ARG<S, A> arg = abstractor.createArg();
        abstractor.check(arg, prec);
        logger.write(Logger.Level.INFO, "Printing ARG..." + System.lineSeparator());
        Graph g = ArgVisualizer.getDefault().visualize(arg);
        logger.write(Logger.Level.INFO, GraphvizWriter.getInstance().writeString(g) + System.lineSeparator());
        logger.write(Logger.Level.INFO, "-----------------------");

        // traces to end nodes/deadlocks
        // finds all possible traces, as nodes have each a single parent
        // and they just get covered with another node when they should have more with another node
        // to which we also generate a trace
        Stream<ArgNode<S, A>> nodeStream = arg.getNodes().filter(saArgNode -> saArgNode.children().findAny().isEmpty());

        traces = nodeStream.map(ArgTrace::to).map(ArgTrace::toTrace).toList();
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
