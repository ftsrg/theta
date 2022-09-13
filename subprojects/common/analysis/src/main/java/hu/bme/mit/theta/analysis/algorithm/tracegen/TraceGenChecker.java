package hu.bme.mit.theta.analysis.algorithm.tracegen;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.*;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

        // traces to end nodes/deadlocks
        // finds all possible traces, as nodes have each a single parent
        // and they just get covered with another node when they should have more with another node
        // to which we also generate a trace

        // TODO XSTS SPECIFIC for now! collecting nodes that look like there should be traces to it, but there isn't
        // this is due to the trans-env-trans-env nature of XSTS (there are nodes without outgoing edges that are covered that are not deadlock states in reality)
        List<ArgNode<S,A>> badNodes = new ArrayList<>();
        arg.getInitNodes().forEach(node -> removeBackwardsCoveredBy(node, badNodes));

        // getting the traces
        List<ArgNode<S, A>> endNodes = arg.getNodes().filter(saArgNode -> saArgNode.isLeaf()).collect(Collectors.toList());
        List<ArgNode<S, A>> filteredEndNodes = new ArrayList<>();
        endNodes.forEach(endNode -> {
            if(badNodes.contains(endNode)) {
                ArgNode<S, A> parent = endNode.getParent().get();
                if(parent.getParent().isPresent()) {
                    ArgNode<S, A> grandParent = parent.getParent().get();
                    if(parent.getOutEdges().count() == 1 && grandParent.getOutEdges().count() == 1) {
                        filteredEndNodes.add(grandParent);
                    }
                }
            } else {
                filteredEndNodes.add(endNode);
            }
        });

        // filter 2, optional, to get full traces even where there is coverage
        boolean getFullTraces = true; // TODO make this a configuration option
        List<ArgNode<S, A>> coveredEndNodes = new ArrayList<>();
        if(getFullTraces) {
            for (ArgNode<S, A> node : filteredEndNodes) {
                if(node.isCovered()) {
                    // and covered-by edge is a cross-edge:
                    ArgNode<S, A> coveringNode = node.getCoveringNode().get();
                    Optional<ArgNode<S, A>> parentNode = node.getParent();
                    boolean crossEdge = true;
                    while(parentNode.isPresent()) {
                        if(parentNode.equals(coveringNode)) {
                            // not a cross edge
                            crossEdge = false;
                            break;
                        }
                        parentNode = parentNode.get().getParent();
                    }

                    if(crossEdge) {
                        coveredEndNodes.add(node);
                    }
                }
            }
            filteredEndNodes.removeAll(coveredEndNodes);
        }

        traces = filteredEndNodes.stream().map(ArgTrace::to).map(ArgTrace::toTrace).toList();

        if(getFullTraces) {
            // TODO add full traces back based on coveredEndNodes
            for (ArgNode<S, A> coveredNode : coveredEndNodes) {
                ArgNode<S, A> coveringNode = coveredNode.getCoveringNode().get();
                AdvancedArgTrace<S, A> part1 = AdvancedArgTrace.to(coveredNode);
                AdvancedArgTrace<S, A> part2 = AdvancedArgTrace.fromTo(coveringNode, );
                // TODO missing edge
            }
        }

        return SafetyResult.unsafe(this.traces.get(0), ARG.create((state1, state2) -> false)); // TODO: this is only a placeholder
    }

    private void removeBackwardsCoveredBy(ArgNode<S, A> node, List<ArgNode<S,A>> badNodes) {
        if(node.isLeaf()) {
            ArgNode<S, A> parent = node.getParent().get();
            if(node.isCovered() && parent.getParent().get() == node.getCoveringNode().get()) {
                // bad node, needs to be removed
                badNodes.add(node);
            }
        }
        else {
            node.children().forEach(child -> removeBackwardsCoveredBy(child, badNodes));
        }
    }

    @Override
    public String toString() {
        // TODO
        return super.toString();
    }
}
