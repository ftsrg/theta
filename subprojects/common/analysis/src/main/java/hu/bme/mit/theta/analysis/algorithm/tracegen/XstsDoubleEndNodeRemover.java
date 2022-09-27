package hu.bme.mit.theta.analysis.algorithm.tracegen;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;

import java.util.ArrayList;
import java.util.List;

public class XstsDoubleEndNodeRemover<S extends ExprState, A extends StmtAction> {
    public static <S extends ExprState, A extends StmtAction> List<ArgNode<S,A>> collectBadNodes(ARG<S,A> arg) {
        // TODO XSTS SPECIFIC for now! collecting nodes that look like there should be traces to it, but there isn't
        // this is due to the trans-env-trans-env nature of XSTS (there are nodes without outgoing edges that are covered that are not deadlock states in reality)
        XstsDoubleEndNodeRemover<S, A> instance = new XstsDoubleEndNodeRemover<S, A>();
        List<ArgNode<S, A>> badNodes = new ArrayList<>();
        arg.getInitNodes().forEach(node -> instance.removeBackwardsCoveredBy(node, badNodes));
        return badNodes;
    }

    private void removeBackwardsCoveredBy(ArgNode<S, A> node, List<ArgNode<S,A>> badNodes) {
        // parent & grandparent check: because in a really small model/small trace (3-4 nodes) there is no (grand)parent, but those are not bad nodes then
        if(node.isLeaf() && node.getParent().isPresent()  && node.getParent().get().getParent().isPresent()) {
            ArgNode<S, A> parent = node.getParent().get();
            if(node.isCovered() && parent.getParent().get() == node.getCoveringNode().get()) { // node is covered and parent is checked above
                // bad node, needs to be removed
                badNodes.add(node);
            }
        }
        else {
            node.children().forEach(child -> removeBackwardsCoveredBy(child, badNodes));
        }
    }

}
