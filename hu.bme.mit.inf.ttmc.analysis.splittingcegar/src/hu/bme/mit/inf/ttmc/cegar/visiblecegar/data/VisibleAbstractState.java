package hu.bme.mit.inf.ttmc.cegar.visiblecegar.data;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Represents an abstract state of the variable-visibility based CEGAR.
 *
 * @author Akos
 */
public class VisibleAbstractState implements AbstractState {
	private final AndExpr expression; // Expression representing the state
	private boolean isInitial; // Is the state initial
	private final List<VisibleAbstractState> successors; // List of successors
	private boolean isPartOfCounterexample; // Is the state part of a counterexample (for visualization)

	/**
	 * Constructor from a model. A reference to the system is required in order
	 * to remove the invisible variables
	 *
	 * @param model
	 *            Model
	 * @param system
	 *            Reference to the system
	 * @param isInitial
	 *            Is the state initial
	 */
	public VisibleAbstractState(final AndExpr expression, final boolean isInitial) {
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.isPartOfCounterexample = false;
		this.expression = expression;
	}

	/**
	 * Get the expression representing this abstract state
	 *
	 * @return Expression representing this abstract state
	 */
	public AndExpr getExpression() {
		return expression;
	}

	@Override
	public boolean isInitial() {
		return isInitial;
	}

	/**
	 * Set whether this abstract state is initial
	 *
	 * @param isInitial
	 *            True if initial, false otherwise
	 */
	public void setInitial(final boolean isInitial) {
		this.isInitial = isInitial;
	}

	/**
	 * Get the list of successors
	 *
	 * @return List of successors
	 */
	@Override
	public List<VisibleAbstractState> getSuccessors() {
		return successors;
	}

	/**
	 * Add a successor state
	 *
	 * @param successor
	 *            State to be added as a successor
	 */
	public void addSuccessor(final VisibleAbstractState successor) {
		successors.add(successor);
	}

	@Override
	public boolean isPartOfCounterexample() {
		return isPartOfCounterexample;
	}

	/**
	 * Set whether the state is part of a counterexample
	 *
	 * @param isPartOfCounterexample
	 *            True if the state is part of a counterexample, false otherwise
	 */
	public void setPartOfCounterExample(final boolean isPartOfCounterexample) {
		this.isPartOfCounterexample = isPartOfCounterexample;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null)
			return false;
		if (!(obj instanceof VisibleAbstractState))
			return false;
		return expression.equals(((VisibleAbstractState) obj).expression);
	}

	@Override
	public int hashCode() {
		return expression.toString().hashCode();
	}

	@Override
	public String toString() {
		return expression.toString() + (isInitial ? ", initial" : "");
	}

	@Override
	public Expr<? extends BoolType> createExpression(final STSManager manager) {
		return expression;
	}

	/**
	 * Create string id
	 *
	 * @return String id
	 */
	public String createId() {
		final StringBuilder ret = new StringBuilder("");

		for (final Expr<?> ex : expression.getOps())
			ret.append(((EqExpr) ex).getRightOp());
		return ret.toString();
	}
}
