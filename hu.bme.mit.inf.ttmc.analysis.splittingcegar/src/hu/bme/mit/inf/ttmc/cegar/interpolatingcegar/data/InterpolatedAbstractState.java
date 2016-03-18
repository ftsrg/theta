package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Represents an abstract state of the interpolated CEGAR algorithm
 *
 * @author Akos
 */
public class InterpolatedAbstractState implements IAbstractState {
	private final List<Expr<? extends BoolType>> labels; // List of labels
	private final List<InterpolatedAbstractState> successors; // List of successors
	private final List<InterpolatedAbstractState> predecessors; // List of predecessors
	private boolean isInitial; // Is the state initial
	private BitSet bitset; // Bitset storing the formulas in a compact way
	private String explicitValues; // Storing explicit values in a compact way
	private boolean isPartOfCounterExample;
	private int exploredIndex;

	/**
	 * Constructor
	 */
	public InterpolatedAbstractState() {
		labels = new ArrayList<>();
		successors = new ArrayList<>();
		predecessors = new ArrayList<>();
		isInitial = false;
		this.bitset = new BitSet();
		this.explicitValues = "";
		this.isPartOfCounterExample = false;
		exploredIndex = -1;
	}

	@Override
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
	 * Get the list of labels
	 *
	 * @return List of labels
	 */
	public List<Expr<? extends BoolType>> getLabels() {
		return labels;
	}

	@Override
	public List<InterpolatedAbstractState> getSuccessors() {
		return successors;
	}

	/**
	 * Add a successor state
	 *
	 * @param successor
	 *            State to be added
	 */
	public void addSuccessor(final InterpolatedAbstractState successor) {
		successors.add(successor);
	}

	/**
	 * Get the list of predecessors
	 *
	 * @return List of predecessors
	 */
	public List<InterpolatedAbstractState> getPredecessors() {
		return predecessors;
	}

	/**
	 * Add a predecessor state
	 *
	 * @param predecessor
	 *            State to be added
	 */
	public void addPredecessor(final InterpolatedAbstractState predecessor) {
		predecessors.add(predecessor);
	}

	/**
	 * Create a new abstract state by copying the labels and adding a new label
	 *
	 * @param label
	 *            The new label to be added
	 * @return New abstract state with the extra label
	 */
	public InterpolatedAbstractState cloneAndAdd(final Expr<? extends BoolType> label) {
		final InterpolatedAbstractState ret = new InterpolatedAbstractState();
		ret.labels.addAll(this.labels);
		ret.labels.add(label);
		ret.bitset = (BitSet) this.bitset.clone(); // Clone bitset
		ret.bitset.set(ret.labels.size() - 1, !(label instanceof NotExpr)); // Set new bit
		ret.explicitValues = this.explicitValues;
		return ret;
	}

	/**
	 * Create a new abstract state by copying the labels and adding explicit
	 * variables
	 *
	 * @param label
	 *            Expression containing the value mapping
	 * @return New abstract state with the new explicit variables
	 */
	public InterpolatedAbstractState cloneAndAddExplicit(final AndExpr label) {
		final InterpolatedAbstractState ret = new InterpolatedAbstractState();
		ret.labels.addAll(this.labels);
		ret.labels.add(0, label); // Insert new label to the beginning
		ret.bitset = (BitSet) this.bitset.clone();
		for (final Expr<? extends BoolType> ex : label.getOps())
			ret.explicitValues += ((EqExpr) ex).getRightOp();
		ret.explicitValues += this.explicitValues;

		return ret;
	}

	/**
	 * Create a new abstract state by copying the labels and adding a new label
	 *
	 * @param label
	 *            The new label to be added
	 * @return New abstract state with the extra label
	 */
	public InterpolatedAbstractState refine(final Expr<? extends BoolType> label) {
		// Currently refinement is the same as 'cloneAndAdd', but a different
		// interface is kept, if in the future this changes
		return cloneAndAdd(label);
	}

	@Override
	public String toString() {
		final StringBuilder ret = new StringBuilder("State: { Labels: {");
		for (final Expr<? extends BoolType> label : labels)
			ret.append(label.toString()).append(" ");
		ret.append("}, Successors: " + successors.size() + (isInitial ? ", Initial" : "") + " }");
		return ret.toString();
	}

	/**
	 * Create string id
	 *
	 * @return String id
	 */
	public String createId() {
		final StringBuilder ret = new StringBuilder(explicitValues);
		for (int i = 0; i < labels.size(); ++i)
			ret.append(bitset.get(i) ? "1" : "0");
		return ret.toString();
	}

	@Override
	public Expr<? extends BoolType> createExpression(final STSManager manager) {
		return manager.getExprFactory().And(labels);
	}

	@Override
	public boolean isPartOfCounterexample() {
		return isPartOfCounterExample;
	}

	/**
	 * Set whether the state is part of a counterexample
	 *
	 * @param isPartOfCounterexample
	 *            True if it is a part of a counterexample, false otherwise
	 */
	public void setPartOfCounterexample(final boolean isPartOfCounterexample) {
		this.isPartOfCounterExample = isPartOfCounterexample;
	}

	/**
	 * Get the index of the state when it was explored
	 *
	 * @return Index
	 */
	public int getExploredIndex() {
		return exploredIndex;
	}

	/**
	 * Set the index of the state when it was explored
	 *
	 * @param idx
	 *            Index
	 */
	public void setExploredIndex(final int idx) {
		this.exploredIndex = idx;
	}
}
