package hu.bme.mit.inf.ttmc.cegar.visiblecegar.data;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Represents an abstract state of the variable-visibility based CEGAR.
 */
public class VisibleAbstractState implements AbstractState {
	private final AndExpr expression;
	private boolean isInitial;
	private final List<VisibleAbstractState> successors;
	private boolean isPartOfCounterexample; // for visualization

	public VisibleAbstractState(final AndExpr expression, final boolean isInitial) {
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.isPartOfCounterexample = false;
		this.expression = expression;
	}

	public AndExpr getExpression() {
		return expression;
	}

	@Override
	public boolean isInitial() {
		return isInitial;
	}

	public void setInitial(final boolean isInitial) {
		this.isInitial = isInitial;
	}

	@Override
	public List<VisibleAbstractState> getSuccessors() {
		return successors;
	}

	public void addSuccessor(final VisibleAbstractState successor) {
		successors.add(checkNotNull(successor));
	}

	@Override
	public boolean isPartOfCounterexample() {
		return isPartOfCounterexample;
	}

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

	public String createId() {
		final StringBuilder ret = new StringBuilder("");

		for (final Expr<?> ex : expression.getOps())
			ret.append(((EqExpr) ex).getRightOp()).append(" ");
		return ret.toString();
	}
}
