package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

public interface Castable<SourceType extends Castable<SourceType>> extends Type {

	public <TargetType extends Type> Expr<TargetType> Cast(Expr<SourceType> op, final TargetType type);

}
