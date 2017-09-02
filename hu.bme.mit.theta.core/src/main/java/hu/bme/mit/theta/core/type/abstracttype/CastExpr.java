package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnaryExpr;

public abstract class CastExpr<SourceType extends Castable<SourceType>, TargetType extends Type>
		extends UnaryExpr<SourceType, TargetType> {

	public CastExpr(final Expr<SourceType> op) {
		super(op);
	}

}
