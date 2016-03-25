package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.utils;

import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractState;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ClusteredAbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data.ComponentAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.graph.Node;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

import java.util.Collection;

/**
 * Helper class for converting a (clustered) abstract Kripke structure
 * into a general graph representation that a visualizer can draw.
 * @author Akos
 */
public class VisualizationHelper {
	/**
	 * Convert clustered abstract Kripke structures into a graph
	 * @param system Clustered abstract system
	 * @param visualizer Visualizer
	 * @param level Minimal level of logging
	 */
	public static void visualizeAbstractKripkeStructures(ClusteredAbstractSystem system, Visualizer visualizer, int level) {
		if(level > visualizer.getMinLevel()) return;

		Graph g = new Graph("KS", "KS");

		// Loop through clusters
		int clusterCount = 0;
		for(KripkeStructure<ComponentAbstractState> ks : system.getAbstractKripkeStructures()){
			// Create a cluster
			ClusterNode cn = new ClusterNode("cluster_" + clusterCount, "Cluster " + clusterCount, "black", "", "", false);
			g.addNode(cn);
			++clusterCount;
			// Loop through states in the cluster
			for(ComponentAbstractState s0 : ks.getStates()){
				StringBuilder labelString = new StringBuilder("");
				for(Expr<? extends Type> label : s0.getLabels()) labelString.append(label).append(" ");
				// Create node for state
				Node n = new Node("s_" + s0.createId(), labelString.toString(), "", "", "", s0.isInitial());
				cn.addSubNode(n);
				// Add arcs for successor states
				for(ComponentAbstractState s1 : s0.getSuccessors())
					n.addSuccessor("s_" + s1.createId(), "");
			}
		}
		
		visualizer.visualize(g);
	}

	/**
	 * Convert the explored composite state space into a graph
	 * @param abstractStates Set of explored states
	 * @param visualizer Visualizer
	 * @param level Minimal level of logging
	 */
	public static void visualizeCompositeAbstractKripkeStructure( Collection<ClusteredAbstractState> abstractStates, Visualizer visualizer, int level) {
		if(level > visualizer.getMinLevel()) return;

		Graph g = new Graph("KS", "KS");
		
		// Loop through explored states
		for(ClusteredAbstractState s0 : abstractStates){
			StringBuilder labelString = new StringBuilder("");
			for(ComponentAbstractState as : s0.getStates()) labelString.append(as.toShortString()).append(" ");
			// Create node for state
			Node n = new Node("s_" + s0.createId(), labelString.toString(), "", s0.isPartOfCounterexample() ? "red" : "", "", s0.isInitial());
			g.addNode(n);
			// Add arcs for successor states
			for(ClusteredAbstractState s1 : s0.getSuccessors()) n.addSuccessor("s_" + s1.createId(), "");
		}
		visualizer.visualize(g);

	}
}
