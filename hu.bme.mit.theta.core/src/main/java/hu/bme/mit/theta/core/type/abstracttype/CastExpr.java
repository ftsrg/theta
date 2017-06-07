package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.UnaryExpr;

public abstract class CastExpr<SourceType extends Type, TargetType extends Type>
		extends UnaryExpr<SourceType, TargetType> {

	public CastExpr(final Expr<SourceType> op) {
		super(op);
	}

}
