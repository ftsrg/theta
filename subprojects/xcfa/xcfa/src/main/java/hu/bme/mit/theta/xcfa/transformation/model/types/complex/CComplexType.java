package hu.bme.mit.theta.xcfa.transformation.model.types.complex;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

import java.util.List;
import java.util.Optional;

public abstract class CComplexType {
	private final CSimpleType origin;

	protected CComplexType(CSimpleType origin) {
		this.origin = origin;
	}

	public CSimpleType getOrigin() {
		return origin;
	}

	public Stmt getLimit() {
		throw new RuntimeException("Limits are not supported for this type!");
	}

	public Expr<?> getNullValue() {
		throw new RuntimeException("Default values are not applicable for this type!");
	}

	public Expr<?> getUnitValue() {
		throw new RuntimeException("Default values are not applicable for this type!");
	}

	public AssumeStmt wrapAround(Expr<?> expr) {
		throw new RuntimeException("Wraparound statements are not supported for this type!");
	}

	public <T extends Type> Expr<T> castTo(Expr<T> expr) {
		throw new RuntimeException("Casting is not supported for this type!");
	}

	public static CComplexType getSmallestCommonType(List<CComplexType> types) {
		CComplexType ret = types.get(0);
		for (int i = 1; i < types.size(); i++) {
			ret = ret.getSmallestCommonType(types.get(i));
		}
		return ret;
	}

	public CComplexType getSmallestCommonType(CComplexType type) {
		throw new RuntimeException("Common type is not applicable for this type!");
	}

	public static CComplexType getType(Expr<?> expr) {
		Optional<Object> cTypeOptional = XcfaMetadata.getMetadataValue(expr,"cType");
		if(cTypeOptional.isPresent() && cTypeOptional.get() instanceof CComplexType) {
			return (CComplexType) cTypeOptional.get();
		} else throw new RuntimeException("Type not known!");
	}

	public static CComplexType getSignedInt() {
		return new CSignedInt(null);
	}

}
