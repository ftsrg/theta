package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Represents a composite abstract state, which is a product of
 * ComponentAbstractStates
 *
 * @author Akos
 */
public class ClusteredAbstractState implements AbstractState {
	private final ComponentAbstractState[] states;
	private final boolean isInitial;
	private final List<ClusteredAbstractState> successors;
	private boolean isPartOfCounterexample;

	/**
	 * Constructor, state is not initial by default
	 *
	 * @param stateCount
	 *            Number of contained states
	 */
	public ClusteredAbstractState(final int stateCount) {
		this(stateCount, false);
	}

	/**
	 * Constructor
	 *
	 * @param stateCount
	 *            Number of contained states
	 * @param isInitial
	 *            Is the state initial
	 */
	public ClusteredAbstractState(final int stateCount, final boolean isInitial) {
		this.states = new ComponentAbstractState[stateCount];
		this.isInitial = isInitial;
		this.successors = new ArrayList<ClusteredAbstractState>();
		this.isPartOfCounterexample = false;
	}

	@Override
	public boolean isInitial() {
		return isInitial;
	}

	/**
	 * Get the list of states
	 *
	 * @return List of states
	 */
	public ComponentAbstractState[] getStates() {
		return states;
	}

	@Override
	public List<ClusteredAbstractState> getSuccessors() {
		return successors;
	}

	@Override
	public boolean isPartOfCounterexample() {
		return isPartOfCounterexample;
	}

	/**
	 * Set whether the state part of a counterexample
	 *
	 * @param isPartOfCounterexample
	 *            Is the state part of a counterexample
	 */
	public void setPartOfCounterexample(final boolean isPartOfCounterexample) {
		this.isPartOfCounterexample = isPartOfCounterexample;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null)
			return false;
		if (!(obj instanceof ClusteredAbstractState))
			return false;

		final ClusteredAbstractState other = (ClusteredAbstractState) obj;
		if (states.length != other.states.length)
			return false;

		// Two composite abstract states are equal if they contain the same states
		for (int i = 0; i < states.length; ++i)
			if (!states[i].equals(other.states[i]))
				return false;

		return true;
	}

	@Override
	public String toString() {
		final StringBuilder ret = new StringBuilder("Composite state: {");
		for (int i = 0; i < states.length; ++i) {
			if (i > 0)
				ret.append(" ");
			ret.append(states[i].toShortString());
		}
		if (isInitial)
			ret.append(", Initial");
		return ret.append("}").toString();
	}

	/**
	 * Convert to a short string representation
	 *
	 * @return State as a short string
	 */
	public String toShortString() {
		final StringBuilder ret = new StringBuilder("{");
		for (int i = 0; i < states.length; ++i) {
			if (i > 0)
				ret.append(" ");
			ret.append(states[i].toShortString());
		}
		if (isInitial)
			ret.append(", I");
		return ret.append("}").toString();
	}

	@Override
	public int hashCode() {
		return Arrays.hashCode(states);
	}

	/**
	 * Create string id
	 *
	 * @return String id
	 */
	public String createId() {
		final StringBuilder ret = new StringBuilder("");
		for (int i = 0; i < states.length; ++i) {
			if (i > 0)
				ret.append("_");
			ret.append(states[i].toShortString());
		}
		return ret.toString();
	}

	@Override
	public Expr<? extends BoolType> createExpression(final STSManager manager) {
		final List<Expr<? extends BoolType>> ops = new ArrayList<>();
		for (final ComponentAbstractState cas : states)
			for (final Expr<? extends BoolType> ex : cas.getLabels())
				ops.add(ex);
		return manager.getExprFactory().And(ops);
	}
}
