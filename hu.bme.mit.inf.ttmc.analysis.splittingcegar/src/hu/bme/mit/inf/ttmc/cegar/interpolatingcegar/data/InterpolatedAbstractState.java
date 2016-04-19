package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

/**
 * Represents an abstract state of the interpolated CEGAR algorithm
 */
public class InterpolatedAbstractState implements AbstractState {
	private final List<Expr<? extends BoolType>> labels;
	private final List<InterpolatedAbstractState> successors;
	private final List<InterpolatedAbstractState> predecessors;
	private boolean isInitial;
	private BitSet bitset; // Bitset storing the formulas in a compact way
	private String explicitValues; // Storing explicit values in a compact way
	private boolean isPartOfCounterExample;
	private int exploredIndex;

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

	public void setInitial(final boolean isInitial) {
		this.isInitial = isInitial;
	}

	public List<Expr<? extends BoolType>> getLabels() {
		return labels;
	}

	@Override
	public List<InterpolatedAbstractState> getSuccessors() {
		return successors;
	}

	public void addSuccessor(final InterpolatedAbstractState successor) {
		successors.add(successor);
	}

	public List<InterpolatedAbstractState> getPredecessors() {
		return predecessors;
	}

	public void addPredecessor(final InterpolatedAbstractState predecessor) {
		predecessors.add(predecessor);
	}

	public InterpolatedAbstractState cloneAndAdd(final Expr<? extends BoolType> label) {
		final InterpolatedAbstractState ret = new InterpolatedAbstractState();
		ret.labels.addAll(this.labels);
		ret.labels.add(label);
		ret.bitset = (BitSet) this.bitset.clone(); // Clone bitset
		ret.bitset.set(ret.labels.size() - 1, !(label instanceof NotExpr)); // Set new bit
		ret.explicitValues = this.explicitValues;
		return ret;
	}

	public InterpolatedAbstractState cloneAndAddExplicit(final AndExpr label) {
		final InterpolatedAbstractState ret = new InterpolatedAbstractState();
		ret.labels.addAll(this.labels);
		ret.labels.add(0, label); // Insert new label to the beginning
		ret.bitset = (BitSet) this.bitset.clone();
		for (final Expr<? extends BoolType> ex : label.getOps())
			ret.explicitValues += ((EqExpr) ex).getRightOp() + " ";
		ret.explicitValues += this.explicitValues;

		return ret;
	}

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

	public String createId() {
		final StringBuilder ret = new StringBuilder(explicitValues);
		for (int i = 0; i < bitset.size(); ++i)
			ret.append(bitset.get(i) ? "1" : "0");
		return ret.toString();
	}

	@Override
	public Expr<? extends BoolType> createExpression() {
		return Exprs.And(labels);
	}

	@Override
	public boolean isPartOfCounterexample() {
		return isPartOfCounterExample;
	}

	public void setPartOfCounterexample(final boolean isPartOfCounterexample) {
		this.isPartOfCounterExample = isPartOfCounterexample;
	}

	public int getExploredIndex() {
		return exploredIndex;
	}

	public void setExploredIndex(final int idx) {
		this.exploredIndex = idx;
	}
}
