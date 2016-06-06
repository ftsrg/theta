package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.common.Product2;

public interface ARGLabeling<S extends State, NodeLabel, EdgeLabel, Init, Trans, Target> {

	public NodeLabel getLabelForInitNode(ARGNode<? extends S, NodeLabel, EdgeLabel> initNode, Init init, Target target);

	public Product2<EdgeLabel, NodeLabel> getLabelForSuccNode(ARGNode<? extends S, NodeLabel, EdgeLabel> succNode,
			Trans trans, Target target);

}
