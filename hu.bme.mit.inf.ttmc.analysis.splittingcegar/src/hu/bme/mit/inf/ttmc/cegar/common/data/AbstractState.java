package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

/**
 * Common interface for abstract states.
 */
public interface AbstractState {

	Expr<? extends BoolType> createExpression();

	boolean isInitial();

	boolean isPartOfCounterexample();

	List<? extends AbstractState> getSuccessors();
}
