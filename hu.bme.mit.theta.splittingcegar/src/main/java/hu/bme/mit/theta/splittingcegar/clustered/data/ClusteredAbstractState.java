package hu.bme.mit.theta.splittingcegar.clustered.data;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;

/**
 * Represents a composite abstract state, which is a product of
 * ComponentAbstractStates.
 */
public class ClusteredAbstractState implements AbstractState {
	private final ComponentAbstractState[] states;
	private final boolean isInitial;
	private final List<ClusteredAbstractState> successors;
	private boolean isPartOfCounterexample;

	public ClusteredAbstractState(final int containedStateCount) {
		this(containedStateCount, false);
	}

	public ClusteredAbstractState(final int containedStateCount, final boolean isInitial) {
		this.states = new ComponentAbstractState[containedStateCount];
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.isPartOfCounterexample = false;
	}

	@Override
	public boolean isInitial() {
		return isInitial;
	}

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

		// Two composite abstract states are equal if they contain the same
		// states
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
	public Expr<BoolType> createExpression() {
		final List<Expr<BoolType>> ops = new ArrayList<>();
		for (final ComponentAbstractState cas : states)
			for (final Expr<BoolType> ex : cas.getLabels())
				ops.add(ex);
		return And(ops);
	}
}
