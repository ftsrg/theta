package hu.bme.mit.theta.analysis.algorithm.tracegen;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

public class TraceGenChecker <S extends ExprState, A extends StmtAction, P extends Prec> implements SafetyChecker<S, A, P> {
    private final Logger logger;
    private final LTS<S, A> lts;
    private final InitFunc<S, P> initFunc;
    private final TransFunc<S, A, P> transFunc;
    private final Predicate<S> unsafePredicate;
    private final Solver solver;

    private TraceGenChecker(final Logger logger,
                            final LTS<S, A> lts,
                            final InitFunc<S, P> initFunc,
                            final TransFunc<S, A, P> transFunc,
                            final Predicate<S> unsafePredicate,
                            final Solver solver) {
        this.logger = logger;
        this.lts = lts;
        this.initFunc = initFunc;
        this.transFunc = transFunc;
        this.unsafePredicate = unsafePredicate;
        this.solver = solver;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> TraceGenChecker create(final Logger logger,
                                                                                                     final LTS<S, A> lts,
                                                                                                     final InitFunc<S, P> initFunc,
                                                                                                     final TransFunc<S, A, P> transFunc,
                                                                                                     final Predicate<S> unsafePredicate,
                                                                                                     final Solver solver) {
        return new TraceGenChecker(logger, lts, initFunc, transFunc, unsafePredicate, solver);
    }

    private final List<Trace<S,A>> traces = new ArrayList<>();

    @Override
    public SafetyResult<S, A> check(P prec) {
        if(prec.getUsedVars().isEmpty()) throw new AssertionError("The precision used for trace generation should be explicit and empty!");

        logger.write(Logger.Level.INFO, "Configuration: %s%n", this);
        generateTraces(prec); // generates traces and puts them into the member list traces
        for (Trace<S, A> trace : traces) {
            System.err.println(trace);
        }
        return SafetyResult.unsafe(traces.get(0), ARG.create((state1, state2) -> false)); // TODO: this is only a placeholder
    }

    private void generateTraces(P prec) {
        final Collection<? extends S> initStates = initFunc.getInitStates(prec);
        traces.clear();
        logger.write(Logger.Level.MAINSTEP, "Generating traces...");

        for (S initState : initStates) {
            logger.write(Logger.Level.SUBSTEP, "Starting traces from %s...", initState);
            final Deque<S> states = new ArrayDeque<>();
            states.push(initState);
            final Deque<A> actions = new ArrayDeque<>();
            step(prec, states, actions);
        }

        logger.write(Logger.Level.MAINSTEP, "Generating traces done, generated %d traces", traces.size());
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

    private void step(P prec, Deque<S> states, Deque<A> actions) {
        S state = states.getLast();
        final Collection<A> enabledActions = lts.getEnabledActionsFor(state);
        if(enabledActions.isEmpty()) {
            logger.write(Logger.Level.INFO, "Generated next trace");
            Trace<S, A> t = Trace.of(states.stream().toList(), actions.stream().toList());
            if(feasibilityCheck(t, solver)) {
                traces.add(t);
            }
        } else {
            for(A a : enabledActions) {
                actions.push(a);
                Collection<? extends S> succStates = transFunc.getSuccStates(state, a, prec);
                for (S succState : succStates) {
                    states.push(succState);
                    step(prec, states, actions);
                    states.pop();
                }
                actions.pop();
            }
        }
    }

    @Override
    public String toString() {
        // TODO
        return super.toString();
    }
}
