package hu.bme.mit.inf.theta.frontend.ir.node;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;

/**
 * This interface represents a branching terminator node which selects its target based on the value of an expression
 */
public interface ConditionalTerminatorNode extends TerminatorIrNode {

	public Expr<? extends Type> getCondition();

}
