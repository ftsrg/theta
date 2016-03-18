package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;

/**
 * Common interface for abstract states.
 *
 * @author Akos
 */
public interface IAbstractState {
	/**
	 * Convert state to expression
	 *
	 * @return Expression representation of the state
	 */
	Expr<? extends BoolType> createExpression(STSManager manager);

	/**
	 * Get whether the state is initial
	 *
	 * @return True if the state is initial, false otherwise
	 */
	boolean isInitial();

	/**
	 * Get whether the state part of a counterexample
	 *
	 * @return True if the state is part of a counterexample, false otherwise
	 */
	boolean isPartOfCounterexample();

	/**
	 * Get the list of successors
	 *
	 * @return List of successors
	 */
	List<? extends IAbstractState> getSuccessors();
}
