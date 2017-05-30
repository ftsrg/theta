package hu.bme.mit.theta.splittingcegar.clustered.data;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.NotExpr;

public class ComponentAbstractState {
	private final List<Expr<? extends BoolType>> labels;
	private final List<ComponentAbstractState> successors;
	private boolean isInitial;
	private BitSet bitset; // Bitset storing the formulas in a compact way
	private final Cluster cluster;
	private final List<Integer> refinementIndicies; // Indices for the abstraction refinement

	public ComponentAbstractState(final Cluster cluster) {
		this(cluster, false);
	}

	public ComponentAbstractState(final Cluster cluster, final boolean isInitial) {
		this.cluster = checkNotNull(cluster);
		labels = new ArrayList<>(cluster.getFormulaCount());
		successors = new ArrayList<ComponentAbstractState>();
		this.isInitial = isInitial;
		this.bitset = new BitSet(cluster.getFormulaCount());
		this.refinementIndicies = new ArrayList<Integer>();
	}

	public List<Expr<? extends BoolType>> getLabels() {
		return labels;
	}

	public List<ComponentAbstractState> getSuccessors() {
		return successors;
	}

	public boolean isInitial() {
		return isInitial;
	}

	public void setInitial(final boolean isInitial) {
		this.isInitial = isInitial;
	}

	public Cluster getCluster() {
		return cluster;
	}

	public ComponentAbstractState cloneAndAdd(final Expr<? extends BoolType> label) {
		checkNotNull(label);
		final ComponentAbstractState ret = new ComponentAbstractState(cluster);
		ret.labels.addAll(this.labels);
		ret.labels.add(label);
		ret.bitset = (BitSet) this.bitset.clone(); // Clone bitset
		ret.bitset.set(ret.labels.size() - 1, !(label instanceof NotExpr)); // Set new bit
		return ret;
	}

	public ComponentAbstractState refine(final int index, final Expr<? extends BoolType> label) {
		checkNotNull(label);
		final ComponentAbstractState ret = new ComponentAbstractState(cluster);
		ret.labels.addAll(this.labels);
		ret.labels.add(label);
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
		if (other.cluster.getClusterId() != this.cluster.getClusterId())
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

	public String toShortString() {
		final StringBuilder ret = new StringBuilder("");
		for (int i = 0; i < cluster.getFormulaCount(); ++i)
			ret.append(bitset.get(i) ? "1" : "0");
		for (final Integer i : refinementIndicies)
			ret.append("r").append(i);
		return ret.toString();
	}

	public String createId() {
		return cluster.getClusterId() + "_" + toShortString();
	}
}
