package hu.bme.mit.theta.analysis.algorithm.tracegen;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.io.BufferedReader;
import java.io.IOError;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

public class XstsDoubleEndNodeRemover<S extends ExprState, A extends StmtAction> {
    static <S extends ExprState, A extends StmtAction> List<ArgNode<S,A>> collectBadNodes(ARG<S,A> arg) {
        // TODO XSTS SPECIFIC for now! collecting nodes that look like there should be traces to it, but there isn't
        // this is due to the trans-env-trans-env nature of XSTS (there are nodes without outgoing edges that are covered that are not deadlock states in reality)
        XstsDoubleEndNodeRemover<S, A> instance = new XstsDoubleEndNodeRemover<S, A>();
        List<ArgNode<S, A>> badNodes = new ArrayList<>();
        arg.getInitNodes().forEach(node -> instance.removeBackwardsCoveredBy(node, badNodes, false));
        return badNodes;
    }

    private void removeBackwardsCoveredBy(ArgNode<S, A> node, List<ArgNode<S,A>> badNodes, boolean isLastInternal) {
        // parent & grandparent check: because in a really small model/small trace (3-4 nodes) there is no (grand)parent, but those are not bad nodes then
        if(isLastInternal && node.isLeaf() && node.getParent().isPresent() && node.getParent().get().getParent().isPresent()) {
            ArgNode<S, A> parent = node.getParent().get();
            ArgNode<S, A> grandParent = node.getParent().get().getParent().get();
            if(node.isCovered() && parent.getParent().get() == node.getCoveringNode().get()) { // node is covered and parent is checked above
                // bad node, needs to be removed
                badNodes.add(node);
            }
        }
        else {
            node.children().forEach(child -> removeBackwardsCoveredBy(child, badNodes, !isLastInternal));
        }
    }

    static <S extends ExprState, A extends StmtAction> Trace<S, A> filterSuperfluousEndNode(Trace<S, A> trace) {
        if(trace.getStates().size()>3) {
            boolean transitionFired = false;
            int size = trace.getStates().size();
            if(trace.getState(size-1).toString().equals(trace.getState(size-3).toString())) {
                BufferedReader bufReader = new BufferedReader(new StringReader(trace.getState(size-2).toString()));
                String line=null;
                try {
                    while( (line=bufReader.readLine()) != null ) {
                        if(line.trim().matches("^\\(__id_.*__.*\strue\\)*$")) transitionFired=true;
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            if(!transitionFired) {
                ArrayList<S> newStates = new ArrayList<>(trace.getStates());
                newStates.remove(newStates.size()-1);
                newStates.remove(newStates.size()-1);
                ArrayList<A> newActions = new ArrayList<>(trace.getActions());
                newActions.remove(newActions.size()-1);
                newActions.remove(newActions.size()-1);
                return Trace.of(newStates, newActions);
            } else {
                return trace;
            }
        } else {
            return trace;
        }
    }
}
