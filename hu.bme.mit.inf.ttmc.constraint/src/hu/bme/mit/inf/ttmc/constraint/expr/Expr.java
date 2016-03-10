package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public interface Expr<ExprType extends Type> {
	
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param);
}
