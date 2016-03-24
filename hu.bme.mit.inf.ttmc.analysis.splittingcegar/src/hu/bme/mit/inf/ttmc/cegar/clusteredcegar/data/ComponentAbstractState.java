package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

/**
 * Represents an abstract state of a cluster.
 *
 * @author Akos
 */
public class ComponentAbstractState {
	private final List<Expr<? extends BoolType>> labels; // List of labels
	private final List<ComponentAbstractState> successors; // Successor states
	private boolean isInitial; // Is the state initial
	private BitSet bitset; // Bitset storing the formulas in a compact way
	private final Cluster cluster; // Cluster the abstract state is belonging to
	private final List<Integer> refinementIndicies; // Indices for the abstraction refinement

	/**
	 * Constructor
	 *
	 * @param cluster
	 *            Cluster of the state
	 */
	public ComponentAbstractState(final Cluster cluster) {
		this(cluster, false);
	}

	/**
	 * Constructor
	 *
	 * @param cluster
	 *            Cluster of the state
	 * @param isInitial
	 *            Is the state initial
	 */
	public ComponentAbstractState(final Cluster cluster, final boolean isInitial) {
		labels = new ArrayList<>(cluster.getFormulaCount());
		successors = new ArrayList<ComponentAbstractState>();
		this.isInitial = isInitial;
		this.bitset = new BitSet(cluster.getFormulaCount());
		this.cluster = cluster;
		this.refinementIndicies = new ArrayList<Integer>();
	}

	/**
	 * Get the list of labels
	 *
	 * @return List of labels
	 */
	public List<Expr<? extends BoolType>> getLabels() {
		return labels;
	}

	/**
	 * Get the list of successors
	 *
	 * @return List of successors
	 */
	public List<ComponentAbstractState> getSuccessors() {
		return successors;
	}

	/**
	 * Get whether the state is initial
	 *
	 * @return True if the state is initial, false otherwise
	 */
	public boolean isInitial() {
		return isInitial;
	}

	/**
	 * Set whether the state is initial
	 *
	 * @param isInitial
	 *            Is the state initial
	 */
	public void setInitial(final boolean isInitial) {
		this.isInitial = isInitial;
	}

	/**
	 * Get the cluster of the abstract state
	 *
	 * @return Cluster of the abstract state
	 */
	public Cluster getCluster() {
		return cluster;
	}

	/**
	 * Create a new abstract state by copying the labels and adding a new label
	 *
	 * @param label
	 *            The new label to be added
	 * @return New abstract state with the extra label
	 */
	public ComponentAbstractState cloneAndAdd(final Expr<? extends BoolType> label) {
		final ComponentAbstractState ret = new ComponentAbstractState(cluster);
		ret.labels.addAll(this.labels); // Clone labels
		ret.labels.add(label); // Add new label
		ret.bitset = (BitSet) this.bitset.clone(); // Clone bitset
		ret.bitset.set(ret.labels.size() - 1, !(label instanceof NotExpr)); // Set new bit
		return ret;
	}

	/**
	 * Refine the abstract state using an expression
	 *
	 * @param index
	 *            Number of the refined state
	 * @param label
	 *            Expression
	 * @return Refined abstract state
	 */
	public ComponentAbstractState refine(final int index, final Expr<? extends BoolType> label) {
		final ComponentAbstractState ret = new ComponentAbstractState(cluster);
		ret.labels.addAll(this.labels); // Clone labels
		ret.labels.add(label); // Add new label
		ret.bitset = (BitSet) this.bitset.clone(); // Clone bitset
		ret.refinementIndicies.addAll(this.refinementIndicies); // Clone refinement indicies
		ret.refinementIndicies.add(index);
		return ret;
	}

	@Override
	public String toString() {
		final StringBuilder ret = new StringBuilder("State: { Labels: {");
		for (final Expr<? extends Type> label : labels)
			ret.append(label.toString()).append(" ");
		ret.append("}, Successors: " + successors.size() + (isInitial ? ", Initial" : "") + " }");
		return ret.toString();
	}

	@Override
	public int hashCode() {
		return bitset.hashCode() * 31 + refinementIndicies.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null)
			return false;
		if (!(obj instanceof ComponentAbstractState))
			return false;

		final ComponentAbstractState other = (ComponentAbstractState) obj;

		// Two abstract states are the same if they belong to the same cluster, the
		// formulas are the same and the abstraction refinement indices are the same
		if (other.cluster.getId() != this.cluster.getId())
			return false;
		if (!this.bitset.equals(other.bitset))
			return false;
		if (this.refinementIndicies.size() != other.refinementIndicies.size())
			return false;
		for (int i = 0; i < this.refinementIndicies.size(); ++i)
			if (this.refinementIndicies.get(i) != other.refinementIndicies.get(i))
				return false;

		return true;
	}

	/**
	 * Convert to short string
	 *
	 * @return Short string representation of the state
	 */
	public String toShortString() {
		final StringBuilder ret = new StringBuilder("");
		for (int i = 0; i < cluster.getFormulaCount(); ++i)
			ret.append(bitset.get(i) ? "1" : "0");
		for (final Integer i : refinementIndicies)
			ret.append("r").append(i);
		return ret.toString();
	}

	/**
	 * Create string id
	 *
	 * @return String id
	 */
	public String createId() {
		return cluster.getId() + "_" + toShortString();
	}
}
