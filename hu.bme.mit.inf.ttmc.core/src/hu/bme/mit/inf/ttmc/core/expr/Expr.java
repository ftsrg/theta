package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

public interface Expr<ExprType extends Type> {

	public ExprType getType();

	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param);
}
