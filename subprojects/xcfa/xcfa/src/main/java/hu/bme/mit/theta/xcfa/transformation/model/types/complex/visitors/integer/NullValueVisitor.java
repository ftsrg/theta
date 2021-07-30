package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class NullValueVisitor extends CComplexType.CComplexTypeVisitor<Void, Expr<?>> {
	public static final NullValueVisitor instance = new NullValueVisitor();
	@Override
	public Expr<?> visit(CInteger type, Void param) {
		return Int(0);
	}
}
