package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface TupleProjExpr extends UnaryExpr<TupleType, Type> {

	public int getIndex();
}
