package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.iteeliminhelpers.PropagateIteVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.iteeliminhelpers.RemoveIteVisitor;

public class IteEliminator {
	private PropagateIteVisitor propagateIteVisitor;
	private RemoveIteVisitor removeIteVisitor;
	
	public IteEliminator(ConstraintManager manager) {
		propagateIteVisitor = new PropagateIteVisitor(manager);
		removeIteVisitor = new RemoveIteVisitor(manager);
	}
	
	public Expr<? extends BoolType> eliminate(Expr<? extends BoolType> expr) {
		return (Expr<? extends BoolType>) expr.accept(propagateIteVisitor, null).accept(removeIteVisitor, null);
	}
}
