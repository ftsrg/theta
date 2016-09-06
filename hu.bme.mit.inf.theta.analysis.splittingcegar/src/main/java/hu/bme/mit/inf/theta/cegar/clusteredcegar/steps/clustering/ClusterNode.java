package hu.bme.mit.inf.theta.cegar.clusteredcegar.steps.clustering;

import hu.bme.mit.inf.theta.cegar.clusteredcegar.data.Cluster;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;

/**
 * Represents a cluster node in the disjoint-set data structure
 * 
 * @author Akos
 */
public class ClusterNode {
	private Cluster cluster;
	private ClusterNode parent;

	/**
	 * Create a cluster from a single variable
	 * 
	 * @param vd
	 *            Variable declaration
	 */
	public ClusterNode(final VarDecl<? extends Type> vd) {
		this.cluster = new Cluster();
		this.cluster.getVars().add(vd);
		this.parent = null;
	}

	/**
	 * Get the cluster
	 * 
	 * @return Cluster
	 */
	public Cluster getCluster() {
		return cluster;
	}

	/**
	 * Set the cluster
	 * 
	 * @param cluster
	 *            Cluster
	 */
	public void setCluster(final Cluster cluster) {
		this.cluster = cluster;
	}

	/**
	 * Get the parent cluster
	 * 
	 * @return Parent cluster
	 */
	public ClusterNode getParent() {
		return parent;
	}

	/**
	 * Set the parent cluster
	 * 
	 * @param parent
	 *            Parent cluster
	 */
	public void setParent(final ClusterNode parent) {
		this.parent = parent;
	}
}
