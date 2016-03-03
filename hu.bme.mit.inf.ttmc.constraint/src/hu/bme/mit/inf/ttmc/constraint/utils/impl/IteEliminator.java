package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ite.PropagateIteVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ite.RemoveIteVisitor;

/**
 * If-Then-Else eliminator.
 * @author Akos
 *
 */
public class IteEliminator {
	private PropagateIteVisitor propagateIteVisitor;
	private RemoveIteVisitor removeIteVisitor;
	
	/**
	 * Constructor.
	 * @param manager Constraint manager
	 */
	public IteEliminator(ConstraintManager manager) {
		propagateIteVisitor = new PropagateIteVisitor(manager);
		removeIteVisitor = new RemoveIteVisitor(manager);
	}
	
	/**
	 * Eliminate if-then-else expressions by replacing them with boolean connectives.
	 * @param expr Expression from where ITE has to be eliminated
	 * @return New expression with no ITE
	 */
	@SuppressWarnings("unchecked")
	public Expr<? extends BoolType> eliminate(Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(propagateIteVisitor, null).accept(removeIteVisitor, null);
	}
}
