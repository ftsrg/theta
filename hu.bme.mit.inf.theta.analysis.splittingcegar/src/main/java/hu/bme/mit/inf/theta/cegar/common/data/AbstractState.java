package hu.bme.mit.inf.theta.cegar.common.data;

import java.util.List;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;

/**
 * Common interface for abstract states.
 */
public interface AbstractState {

	Expr<? extends BoolType> createExpression();

	boolean isInitial();

	boolean isPartOfCounterexample();

	List<? extends AbstractState> getSuccessors();
}
