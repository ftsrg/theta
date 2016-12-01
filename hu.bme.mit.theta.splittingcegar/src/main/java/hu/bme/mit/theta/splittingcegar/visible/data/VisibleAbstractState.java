package hu.bme.mit.theta.splittingcegar.visible.data;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;

/**
 * Represents an abstract state of the variable-visibility based CEGAR.
 */
public class VisibleAbstractState implements AbstractState {
	private final Valuation valuation;
	private boolean isInitial;
	private final List<VisibleAbstractState> successors;
	private boolean isPartOfCounterexample; // for visualization

	public VisibleAbstractState(final Valuation expression, final boolean isInitial) {
		this.isInitial = isInitial;
		this.successors = new ArrayList<>();
		this.isPartOfCounterexample = false;
		this.valuation = expression;
	}

	public Valuation getValuation() {
		return valuation;
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
		return valuation.equals(((VisibleAbstractState) obj).valuation);
	}

	@Override
	public int hashCode() {
		return valuation.toString().hashCode();
	}

	@Override
	public String toString() {
		return valuation.toString() + (isInitial ? ", initial" : "");
	}

	@Override
	public Expr<? extends BoolType> createExpression() {
		return valuation.toExpr();
	}

	public String createId() {
		final StringBuilder ret = new StringBuilder("");
		for (final VarDecl<? extends Type> varDecl : valuation.getDecls())
			ret.append(valuation.eval(varDecl).get()).append(" ");
		return ret.toString();
	}
}
