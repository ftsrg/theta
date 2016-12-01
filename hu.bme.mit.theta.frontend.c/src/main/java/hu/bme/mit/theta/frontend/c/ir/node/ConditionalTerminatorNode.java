package hu.bme.mit.theta.frontend.c.ir.node;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

/**
 * This interface represents a branching terminator node which selects its
 * target based on the value of an expression
 */
public interface ConditionalTerminatorNode extends TerminatorIrNode {

	public Expr<? extends Type> getCondition();

}
