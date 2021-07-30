package hu.bme.mit.theta.xcfa.transformation.model.types.complex;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CUnsignedShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CLongDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CReal;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer.CastVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer.LimitVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer.NullValueVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer.TypeVisitor;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer.UnitValueVisitor;
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

	public Expr<?> getNullValue() {
		return this.accept(NullValueVisitor.instance, null);
	}

	public Expr<?> getUnitValue() {
		return this.accept(UnitValueVisitor.instance, null);
	}

	public AssumeStmt limit(Expr<?> expr) {
		return this.accept(LimitVisitor.instance, expr);
	}

	public Expr<?> castTo(Expr<?> expr) {
		return this.accept(CastVisitor.instance, expr);
	}

	public Type getSmtType() {
		return this.accept(TypeVisitor.instance, null);
	}

	public CComplexType getSmallestCommonType(CComplexType type) {
		throw new RuntimeException("Common type is not applicable for this type!");
	}

	public static CComplexType getSmallestCommonType(List<CComplexType> types) {
		CComplexType ret = types.get(0);
		for (int i = 1; i < types.size(); i++) {
			ret = ret.getSmallestCommonType(types.get(i));
		}
		return ret;
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

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	public static class CComplexTypeVisitor<T, R> {
		public R visit(CComplexType type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CVoid type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CReal type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CDouble type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CFloat type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CLongDouble type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CInteger type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CShort type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CSignedShort type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CUnsignedShort type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CLongLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CSignedLongLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CUnsignedLongLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CUnsignedLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CSignedLong type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CInt type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CSignedInt type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CUnsignedInt type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CChar type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CSignedChar type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CUnsignedChar type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
		public R visit(CBool type, T param) {
			throw new UnsupportedOperationException("Not (yet) implemented");
		}
	}

}
