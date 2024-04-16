package hu.bme.mit.theta.analysis.algorithm.tracegeneration;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

public class XstsDoubleEndNodeRemover<S extends ExprState, A extends ExprAction> {
    static <S extends ExprState, A extends ExprAction> List<ArgNode<S,A>> collectBadLeaves(ARG<S,A> arg) {
        // TODO XSTS SPECIFIC for now! collecting nodes that look like there should be traces to it, but shouldn't ("not firing anything" nodes)
        XstsDoubleEndNodeRemover<S, A> instance = new XstsDoubleEndNodeRemover<S, A>();
        List<ArgNode<S, A>> badNodes = new ArrayList<>();
        arg.getNodes().filter(ArgNode::isLeaf).forEach(node -> {
            if(instance.isBadLeaf(node)) { badNodes.add(node); }
        } );
        return badNodes;
    }

    private boolean isLastInternal(ArgNode<S, A> node) {
        return node.getState().toString().contains("last_internal");
    }

    private boolean isBadLeaf(ArgNode<S, A> node) {
        if(isLastInternal(node)) {
            if(node.getParent().isEmpty()) return false;
            ArgNode<S, A> parent = node.getParent().get();
            if(parent.getParent().isEmpty()) return false;
            ArgNode<S, A> grandParent = node.getParent().get().getParent().get();
            if(node.isCovered() && parent.getParent().get() == node.getCoveringNode().get()) { // node is covered and parent is checked above
                // bad node
                return true;
            } else {
                return false;
            }
        } else {
            boolean transitionFired = false;
            if(node.getParent().isPresent() && node.getParent().get().getParent().isPresent()) {
                ArgNode<S, A> grandParent = node.getParent().get().getParent().get();
                if(!(node.isCovered() && node.getCoveringNode().get()==grandParent)) return false;

                String state = node.getParent().get().getState().toString();
                BufferedReader bufReader = new BufferedReader(new StringReader(state));
                String line=null;
                try {
                    while( (line=bufReader.readLine()) != null ) {
                        if(line.trim().matches("^.*\\(__id_.*__.*\strue\\).*$")) transitionFired=true;
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
                return !transitionFired; // if no transition was fired (and state not changed), this is a superfluous node
            } else {
                return false;
            }
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
