package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Common interface for abstract states.
 */
public interface AbstractState {

	Expr<? extends BoolType> createExpression(STSManager manager);

	boolean isInitial();

	boolean isPartOfCounterexample();

	List<? extends AbstractState> getSuccessors();
}
