package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ValueVisitor extends CComplexType.CComplexTypeVisitor<String, LitExpr<?>> {
	public static final ValueVisitor instance = new ValueVisitor();
	@Override
	public LitExpr<?> visit(CInteger type, String param) {
		return Int(new BigInteger(param));
	}
}
