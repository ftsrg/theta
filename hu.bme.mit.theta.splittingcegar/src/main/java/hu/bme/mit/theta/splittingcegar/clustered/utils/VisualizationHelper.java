package hu.bme.mit.theta.splittingcegar.clustered.utils;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractState;
import hu.bme.mit.theta.splittingcegar.clustered.data.ClusteredAbstractSystem;
import hu.bme.mit.theta.splittingcegar.clustered.data.ComponentAbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.KripkeStructure;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.ClusterNode;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Graph;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.graph.Node;

/**
 * Helper class for converting a (clustered) abstract Kripke structure into a
 * general graph representation that a visualizer can draw.
 */
public class VisualizationHelper {

	public static void visualizeAbstractKripkeStructures(final ClusteredAbstractSystem system, final Visualizer visualizer, final int level) {
		if (level > visualizer.getMinLevel())
			return;

		final Graph g = new Graph("KS", "KS");

		// Loop through clusters
		int clusterCount = 0;
		for (final KripkeStructure<ComponentAbstractState> ks : system.getAbstractKripkeStructures()) {
			// Create a cluster
			final ClusterNode cn = new ClusterNode("cluster_" + clusterCount, "Cluster " + clusterCount, "black", "", "", false);
			g.addNode(cn);
			++clusterCount;
			// Loop through states in the cluster
			for (final ComponentAbstractState s0 : ks.getStates()) {
				final StringBuilder labelString = new StringBuilder("");
				for (final Expr<? extends Type> label : s0.getLabels())
					labelString.append(label).append(" ");
				// Create node for state
				final Node n = new Node("s_" + s0.createId(), labelString.toString(), "", "", "", s0.isInitial());
				cn.addSubNode(n);
				// Add arcs for successor states
				for (final ComponentAbstractState s1 : s0.getSuccessors())
					n.addSuccessor("s_" + s1.createId(), "");
			}
		}

		visualizer.visualize(g);
	}

	public static void visualizeCompositeAbstractKripkeStructure(final Collection<ClusteredAbstractState> abstractStates, final Visualizer visualizer,
			final int level) {
		if (level > visualizer.getMinLevel())
			return;

		final Graph g = new Graph("KS", "KS");

		// Loop through explored states
		for (final ClusteredAbstractState s0 : abstractStates) {
			final StringBuilder labelString = new StringBuilder("");
			for (final ComponentAbstractState as : s0.getStates())
				labelString.append(as.toShortString()).append(" ");
			// Create node for state
			final Node n = new Node("s_" + s0.createId(), labelString.toString(), "", s0.isPartOfCounterexample() ? "red" : "", "", s0.isInitial());
			g.addNode(n);
			// Add arcs for successor states
			for (final ClusteredAbstractState s1 : s0.getSuccessors())
				n.addSuccessor("s_" + s1.createId(), "");
		}
		visualizer.visualize(g);

	}
}
