package hu.bme.mit.inf.ttmc.constraint.expr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public interface MulExpr<ExprType extends ClosedUnderMul> extends MultiaryExpr<ExprType, ExprType> {
	
	@Override
	public MulExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops);

	@Override
	public default <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
