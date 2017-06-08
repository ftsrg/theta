package hu.bme.mit.theta.splittingcegar.clustered.steps.clustering;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.splittingcegar.clustered.data.Cluster;

/**
 * Cluster creator
 *
 * @author Akos
 */
public class ClusterCreator {

	/**
	 * Create clusters using variables and atomic formulas
	 *
	 * @param variables
	 *            Variables
	 * @param formulas
	 *            Atomic formulas
	 * @return Variable clusters
	 */
	public List<Cluster> getClusters(final Set<VarDecl<?>> variables, final List<Expr<BoolType>> formulas) {
		// Create a separate cluster for each variable
		final Map<VarDecl<?>, ClusterNode> clusters = new HashMap<>();
		for (final VarDecl<?> entry : variables)
			clusters.put(entry, new ClusterNode(entry));

		// Loop through formulas
		for (final Expr<BoolType> ex : formulas) {
			// Get variables and join clusters
			final List<VarDecl<?>> vars = new ArrayList<>(ExprUtils.getVars(ex));
			if (vars.size() == 2)
				joinClusters(clusters.get(vars.get(0)), clusters.get(vars.get(1)));
			else if (vars.size() > 2)
				throw new UnsupportedOperationException("TODO: more than two variables in an atomic formula.");

			// Add formula to cluster
			getCluster(clusters.get(vars.get(0))).getCluster().getFormulas().add(ex);
		}

		// Return only the top-level clusters
		final List<Cluster> ret = new ArrayList<>();
		int nextId = 0;
		for (final VarDecl<?> var : variables) {
			final ClusterNode cn = clusters.get(var);
			if (cn.getParent() == null) {
				cn.getCluster().setId(nextId++);
				ret.add(cn.getCluster());
			}
		}

		return ret;
	}

	/**
	 * Get top-level cluster node
	 *
	 * @param node
	 *            Cluster node
	 * @return Top level cluster node
	 */
	private ClusterNode getCluster(ClusterNode node) {
		while (node.getParent() != null)
			node = node.getParent();
		return node;
	}

	/**
	 * Join clusters
	 *
	 * @param c1
	 *            First cluster
	 * @param c2
	 *            Second cluster
	 */
	private void joinClusters(final ClusterNode c1, final ClusterNode c2) {
		final ClusterNode cn1 = getCluster(c1);
		final ClusterNode cn2 = getCluster(c2);
		if (cn1 != cn2) {
			cn1.setParent(cn2);
			cn2.getCluster().getVars().addAll(cn1.getCluster().getVars());
			cn2.getCluster().getFormulas().addAll(cn1.getCluster().getFormulas());
			cn1.setCluster(null);
		}
	}
}
