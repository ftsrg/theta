package hu.bme.mit.theta.analysis.algorithm.tracegen;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.algorithm.*;
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class TraceGenChecker <S extends ExprState, A extends StmtAction, P extends Prec> implements SafetyChecker<S, A, P> {
    private final Logger logger;
    private boolean getFullTraces = false;
    private final Abstractor<S, A, P> abstractor;

    private TraceGenChecker(final Logger logger,
                            final Abstractor<S, A, P> abstractor, boolean getFullTraces) {
        this.getFullTraces = getFullTraces;
        this.logger = logger;
        this.abstractor = abstractor;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> TraceGenChecker<S,A,P> create(final Logger logger,
                                                                                                     final Abstractor<S,A,P> abstractor, boolean getFullTraces) {
        return new TraceGenChecker<S,A,P>(logger, abstractor, getFullTraces);
    }

    private List<Tuple2<Trace<S,A>, ArgNode<S,A>>> traces = new ArrayList<>();

    public List<Trace<S, A>> getTraces() {
        return traces.stream().map(tuple2 -> tuple2.get1()).toList();
    }

    @Override
    public SafetyResult<S, A> check(P prec) {
        final ARG<S, A> arg = abstractor.createArg();
        abstractor.check(arg, prec);
        logger.write(Logger.Level.INFO, "Printing ARG..." + System.lineSeparator());
        Graph g = ArgVisualizer.getDefault().visualize(arg);
        logger.write(Logger.Level.INFO, GraphvizWriter.getInstance().writeString(g) + System.lineSeparator());

        List<ArgNode<S, A>> badNodes = XstsDoubleEndNodeRemover.collectBadNodes(arg);

        // getting the traces
        List<ArgNode<S, A>> endNodes = arg.getNodes().filter(ArgNode::isLeaf).toList();
        List<ArgNode<S, A>> filteredEndNodes = new ArrayList<>();
        endNodes.forEach(endNode -> {
            if(badNodes.contains(endNode)) {
                if(endNode.getParent().isPresent() && endNode.getParent().get().getParent().isPresent()) {
                    ArgNode<S, A> parent = endNode.getParent().get();
                    ArgNode<S, A> grandParent = endNode.getParent().get().getParent().get();
                    // TODO add justification here
                    if(parent.getOutEdges().count() == 1 && grandParent.getOutEdges().count() == 1) {
                        filteredEndNodes.add(grandParent);
                    }
                } else {
                    throw new RuntimeException("Unexpected error: Bad Nodes should always have parents and grandparents");
                }
            } else {
                filteredEndNodes.add(endNode);
            }
        });

        List<ArgTrace<S, A>> argTraces = new ArrayList<>(filteredEndNodes.stream().map(ArgTrace::to).toList());
        traces.addAll(argTraces.stream().map(argTrace -> Tuple2.of(argTrace.toTrace(), argTrace.node(argTrace.nodes().size()-1))).toList());

        // filter 2, optional, to get full traces even where there is coverage
        if(getFullTraces) {
            traces = modifyToFullTraces(filteredEndNodes, argTraces);
        }

        return SafetyResult.unsafe(this.traces.stream().map(Tuple2::get1).toList().get(0), ARG.create((state1, state2) -> false)); // TODO this is only a placeholder
    }

    private List<ArgNode<S, A>> computeCoveredEndNodes(List<ArgNode<S, A>> filteredEndNodes) {
        List<ArgNode<S, A>> coveredEndNodes = new ArrayList<>();
        for (ArgNode<S, A> node : filteredEndNodes) {
            if(node.isCovered()) {
                // and covered-by edge is a cross-edge:
                ArgNode<S, A> coveringNode = node.getCoveringNode().get(); // check above with isCovered()
                Optional<ArgNode<S, A>> parentNode = node.getParent();
                boolean crossEdge = true;
                while(parentNode.isPresent()) {
                    if(parentNode.get().equals(coveringNode)) {
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
        return coveredEndNodes;
    }

    private List<Tuple2<Trace<S,A>, ArgNode<S,A>>> modifyToFullTraces(List<ArgNode<S, A>> filteredEndNodes, List<ArgTrace<S, A>> argTraces) {
        List<ArgNode<S, A>> remainingCoveredEndNodes;
        List<ArgNode<S, A>> coveredEndNodes = computeCoveredEndNodes(filteredEndNodes);
        while(!coveredEndNodes.isEmpty()) {
            remainingCoveredEndNodes = new ArrayList<>();
            for (ArgNode<S, A> coveredNode : coveredEndNodes) {
                ArgNode<S, A> coveringNode = coveredNode.getCoveringNode().get(); // list only has covered nodes
                AdvancedArgTrace<S, A> part1 = AdvancedArgTrace.to(coveredNode);

                for (ArgTrace<S, A> existingTrace : argTraces) {
                    if (existingTrace.nodes().contains(coveringNode)) {
                        // removing partial trace from traces (longer traces will be added instead)
                        List<Tuple2<Trace<S, A>, ArgNode<S, A>>> tracesToRemove = traces.stream().filter(tuple2 -> tuple2.get2().equals(coveredNode)).toList();
                        if (!tracesToRemove.isEmpty()) { // TODO I am not sure if this will cause any bugs, but I do not see a better solution for now
                            traces.removeAll(tracesToRemove);
                        } else {
                            System.err.println("Partial traces not in list, might have been removed already earlier");
                        }

                        // Getting the separate halves of new trace
                        AdvancedArgTrace<S, A> part2 = AdvancedArgTrace.fromTo(coveringNode, existingTrace.node(existingTrace.nodes().size() - 1));
                        ArgNode<S, A> part2EndNode = part2.node(part2.nodes().size() - 1);

                        ArgNode<S, A> endNode = part2.nodes().get(part2.nodes().size() - 1);
                        if (coveredEndNodes.contains(endNode)) {
                            remainingCoveredEndNodes.add(endNode);
                        }
                        Trace<S, A> part1Trace = part1.toTrace();
                        Trace<S, A> part2Trace = part2.toTrace();

                        // Concatenating states
                        ArrayList<S> lengthenedTraceStates = new ArrayList<>(part1Trace.getStates());
                        lengthenedTraceStates.remove(lengthenedTraceStates.size() - 1);
                        lengthenedTraceStates.addAll(part2Trace.getStates());

                        // Concatenating actions
                        List<A> lengthenedTraceActions = new ArrayList<>(part1Trace.getActions());
                        lengthenedTraceActions.addAll(part2Trace.getActions());

                        Trace<S, A> lengthenedTrace = Trace.of(lengthenedTraceStates, lengthenedTraceActions);
                        traces.add(Tuple2.of(lengthenedTrace, part2EndNode));
                    }
                }
            }
            coveredEndNodes = remainingCoveredEndNodes;
        }
        return traces;
    }
}
