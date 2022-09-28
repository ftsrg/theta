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

import static com.google.common.base.Preconditions.checkState;

public class TraceGenChecker <S extends ExprState, A extends StmtAction, P extends Prec> implements SafetyChecker<S, A, P> {
    private final Logger logger;
    private boolean getFullTraces = false;
    private final Abstractor<S, A, P> abstractor;
    private List<Trace<S,A>> traces = new ArrayList<>();

    private TraceGenChecker(final Logger logger,
                            final Abstractor<S, A, P> abstractor, boolean getFullTraces) {
        this.getFullTraces = getFullTraces;
        this.logger = logger;
        this.abstractor = abstractor;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> TraceGenChecker<S,A,P> create(final Logger logger, final Abstractor<S,A,P> abstractor, boolean getFullTraces) {
        return new TraceGenChecker<S,A,P>(logger, abstractor, getFullTraces);
    }

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

        // bad node: XSTS specific thing, that the last state (last_env nodes) doubles up and the leaf is covered by the
        // last_env before which is superfluous.
        // Possible side effect if not handled: possibly a "non-existing leaf" and superfluous traces or just traces that are 1 longer than they should be
        List<ArgNode<S, A>> badNodes = XstsDoubleEndNodeRemover.collectBadNodes(arg);

        // leaves
        List<ArgNode<S, A>> endNodes = arg.getNodes().filter(ArgNode::isLeaf).toList();
        // TODO might be worth it to create a "mutable ARG" where I can actually remove bad nodes instead - worth to think about
        // leaves, but bad nodes are properly filtered, see bad nodes above
        List<ArgNode<S, A>> filteredEndNodes = filterEndNodes(endNodes, badNodes);

        List<ArgTrace<S, A>> argTraces = new ArrayList<>(filteredEndNodes.stream().map(ArgTrace::to).toList());

        // filter 2, optional, to get full traces even where there is coverage
        if(getFullTraces) {
            traces = modifyToFullTraces(filteredEndNodes, argTraces);
        } else {
            traces = new ArrayList<>(argTraces.stream().map(ArgTrace::toTrace).toList());
        }

        checkState(traces.size()>0, "Generated 0 traces, which should be impossible");
        return SafetyResult.unsafe(this.traces.get(0), ARG.create((state1, state2) -> false)); // this is only a placeholder
    }

    private List<ArgNode<S,A>> filterEndNodes(List<ArgNode<S,A>> endNodes, List<ArgNode<S,A>> badNodes) {
        List<ArgNode<S, A>> filteredEndNodes = new ArrayList<>(); // leaves that are not "bad nodes" or bad nodes' grandparents
        endNodes.forEach(endNode -> {
            if(badNodes.contains(endNode)) {
                if(endNode.getParent().isPresent() && endNode.getParent().get().getParent().isPresent()) {
                    ArgNode<S, A> parent = endNode.getParent().get();
                    ArgNode<S, A> grandParent = endNode.getParent().get().getParent().get();
                    // If the parent & grandparent (same state as the bad node) has no other successors,
                    // the grandparent is the "new leaf"
                    // if there are successors, there is no real leaf here
                    if(grandParent.getOutEdges().count() == 1 && parent.getOutEdges().count() == 1) {
                        filteredEndNodes.add(grandParent);
                    }
                } else {
                    throw new RuntimeException("Unexpected error: bad nodes should always have parents and grandparents");
                }
            } else {
                filteredEndNodes.add(endNode);
            }
        });
        return filteredEndNodes;
    }

    private List<ArgNode<S, A>> computeCrossCoveredEndNodes(List<ArgNode<S, A>> filteredEndNodes) {
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

    private List<Trace<S, A>> modifyToFullTraces(List<ArgNode<S, A>> filteredEndNodes, List<ArgTrace<S, A>> argTraces) {
        List<ArgNode<S, A>> crossCoveredEndNodes = computeCrossCoveredEndNodes(filteredEndNodes);
        // new traces
        List<List<AdvancedArgTrace<S,A>>> newTraces = new ArrayList<>();

        // first iteration on the covered end nodes
        for (ArgNode<S, A> coveredNode : crossCoveredEndNodes) {
            ArgNode<S, A> coveringNode = coveredNode.getCoveringNode().get(); // coveredNode list only has covered nodes
            AdvancedArgTrace<S, A> part1 = AdvancedArgTrace.to(coveredNode);
            for (ArgTrace<S, A> existingTrace : argTraces) {
                if (existingTrace.nodes().contains(coveringNode)) {
                    // Getting the separate halves of new trace
                    AdvancedArgTrace<S, A> part2 = AdvancedArgTrace.fromTo(coveringNode, existingTrace.node(existingTrace.nodes().size() - 1));
                    newTraces.add(List.of(part1,part2)); // in this iteration all of these are only 2 parts, but later on it might become more
                }
            }
        }

        // now we iterate over the new traces until all of them are maximal
        // TODO - lengthening the traces this way is far from being the most efficient, it can easily blow up
        // some kind of smart collecting of partial traces "globally", instead of iteratively and then pairing all of
        // them properly might be faster (not sure)
        // but however we do this, the number of full traces in the result can easily blow up anyways, so I am not sure
        // it would matter much
        boolean tracesChanged = true;
        while(tracesChanged) {
            tracesChanged = false;
            List<List<AdvancedArgTrace<S, A>>> changedTraces = new ArrayList<>();
            for (List<AdvancedArgTrace<S, A>> newTrace : newTraces) {
                ArgNode<S, A> lastNode = getLastNode(newTrace);
                if(crossCoveredEndNodes.contains(lastNode)) { // isCovered() check present
                    ArgNode<S, A> coveringNode = lastNode.getCoveringNode().get();
                    // we can lengthen the new trace more
                    // and it can even branch, so we might add several new traces actually
                    for (ArgTrace<S, A> existingTrace : argTraces) {
                        if (existingTrace.nodes().contains(coveringNode)) {
                            tracesChanged = true;
                            // getting a new part for the trace
                            AdvancedArgTrace<S, A> newPart = AdvancedArgTrace.fromTo(coveringNode, existingTrace.node(existingTrace.nodes().size() - 1));
                            ArrayList<AdvancedArgTrace<S, A>> changedTrace = new ArrayList<>(newTrace);
                            changedTrace.add(newPart);

                            changedTraces.add(changedTrace);
                        }
                    }
                    checkState(tracesChanged, "There should be at least one lengthened trace added here");
                } else {
                    changedTraces.add(newTrace);
                }
            }

            if(tracesChanged) {
                newTraces = changedTraces;
            }
        }

        List<Trace<S,A>> result = new ArrayList<>();
        // concatenating lengthened maximal traces and converting them to state-action traces to add them to the result list
        for (List<AdvancedArgTrace<S, A>> newTrace : newTraces) {
            result.add(concatenateTraces(newTrace));
        }

        // adding traces that did not have to be lengthened to the resulting state-action trace list
        for (ArgTrace<S, A> argTrace : argTraces) {
            if(!crossCoveredEndNodes.contains(argTrace.node(argTrace.nodes().size()-1))) {
                result.add(argTrace.toTrace());
            }
        }
        return result;
    }

    // created for traces that are stored as a list (they are not concatenated yet)
    private ArgNode<S, A> getLastNode(List<AdvancedArgTrace<S, A>> traceList) {
        AdvancedArgTrace<S, A> traces = traceList.get(traceList.size() - 1);
        return traces.node(traces.nodes().size()-1);
    }

    private Trace<S, A> concatenateTraces(List<AdvancedArgTrace<S, A>> parts) {
        checkState(parts.size()>0);
        ArrayList<S> newTraceStates = new ArrayList<>();
        ArrayList<A> newTraceActions = new ArrayList<>();
        for (AdvancedArgTrace<S, A> part : parts) {
            // Concatenating states
            if (newTraceStates.size() > 0) {
                newTraceStates.remove(newTraceStates.size() - 1);
            }
            newTraceStates.addAll(part.toTrace().getStates());

            // Concatenating actions
            newTraceActions.addAll(part.toTrace().getActions());
        }

        return Trace.of(newTraceStates, newTraceActions);
    }
}
