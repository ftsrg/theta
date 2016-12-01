package hu.bme.mit.theta.splittingcegar.common.data;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

/**
 * Common interface for abstract states.
 */
public interface AbstractState {

	Expr<? extends BoolType> createExpression();

	boolean isInitial();

	boolean isPartOfCounterexample();

	List<? extends AbstractState> getSuccessors();
}
