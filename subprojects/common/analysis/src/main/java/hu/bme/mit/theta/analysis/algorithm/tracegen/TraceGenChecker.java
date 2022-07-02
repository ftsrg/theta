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

        // traces to end nodes/deadlocks
        // finds all possible traces, as nodes have each a single parent
        // and they just get covered with another node when they should have more with another node
        // to which we also generate a trace
        Stream<ArgNode<S, A>> nodeStream = arg.getNodes().filter(saArgNode -> saArgNode.children().findAny().isEmpty());

        traces = nodeStream.map(ArgTrace::to).map(ArgTrace::toTrace).toList();
        return SafetyResult.unsafe(this.traces.get(0), ARG.create((state1, state2) -> false)); // TODO: this is only a placeholder
    }

    @Override
    public String toString() {
        // TODO
        return super.toString();
    }
}
