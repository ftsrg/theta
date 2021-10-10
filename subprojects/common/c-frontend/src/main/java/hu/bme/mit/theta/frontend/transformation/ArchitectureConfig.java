package hu.bme.mit.theta.frontend.transformation;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.CastVisitor;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.LimitVisitor;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.NullValueVisitor;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.TypeVisitor;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.UnitValueVisitor;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector.ValueVisitor;

import java.util.LinkedHashMap;
import java.util.Map;

public class ArchitectureConfig {
	public static final ArchitectureType architecture = ArchitectureType.ILP32;
	public static Boolean multiThreading = false;
	public static ArithmeticType arithmetic = ArithmeticType.efficient;


	/**
	 * ILP32 and LP64 Architecture, see here: https://unix.org/whitepapers/64bit.html
	 * Warning note: when deducing type, we assume an ILP32 or an LP64 arch
	 * (e.g. conversion rules would get more complex, if an int isn't at least twice as big as a short)
	 */
	public enum ArchitectureType {
		ILP32(1, 8,16,32,32,64, 24, 8, 53, 11, 113, 15, 65),
		LP64(1, 8,16,32,64,64, 24, 8, 53, 11, 113, 15, 65);

		public final Map<String, Integer> standardTypeSizes = new LinkedHashMap<>();

		ArchitectureType(int _bool, int _char, int _short, int _int, int _long, int _longlong,
						 int _float_significand, int _float_exponent, int _double_significand, int _double_exponent,
						 int _longdouble_significand, int _longdouble_exponend, int _fitsall) {
			standardTypeSizes.put("void", 1);
			standardTypeSizes.put("bool", _bool);
			standardTypeSizes.put("char", _char);
			standardTypeSizes.put("short", _short);
			standardTypeSizes.put("int", _int);
			standardTypeSizes.put("long", _long);
			standardTypeSizes.put("longlong", _longlong);
			standardTypeSizes.put("float_s", _float_significand);
			standardTypeSizes.put("float_e", _float_exponent);
			standardTypeSizes.put("double_s", _double_significand);
			standardTypeSizes.put("double_e", _double_exponent);
			standardTypeSizes.put("longdouble_s", _longdouble_significand);
			standardTypeSizes.put("longdouble_e", _longdouble_exponend);
			standardTypeSizes.put("fitsall", _fitsall);
		}

		public int getBitWidth(String typeName) {
			return standardTypeSizes.get(typeName);
		}
	}

	/**
	 * Which arithmetic type to use:
	 * 	- integer: bitvectors are not supported (e.g. floats, bitwise ops). This is the most performant.
	 * 	- bitvector: every operation is handled through BV primitives. This can handle virtually anything (in scope).
	 * 				 This is not as performant as integer arithmetic.
	 * 	- efficient: Integer when possible, bitvector when necessary - this is the default (and performance-wise best) option
	 */
	public enum ArithmeticType {
		integer,
		bitvector,
		efficient
	}

	public static CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> getCastVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return CastVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.CastVisitor.instance;
	}
	public static CComplexType.CComplexTypeVisitor<Expr<?>, AssumeStmt> getLimitVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return LimitVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.LimitVisitor.instance;
	}
	public static CComplexType.CComplexTypeVisitor<Void, LitExpr<?>>  getNullValueVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return NullValueVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.NullValueVisitor.instance;
	}
	public static CComplexType.CComplexTypeVisitor<Void, LitExpr<?>>  getUnitValueVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return UnitValueVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.UnitValueVisitor.instance;
	}
	public static CComplexType.CComplexTypeVisitor<Void, Type> getTypeVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return TypeVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.TypeVisitor.instance;
	}
	public static CComplexType.CComplexTypeVisitor<String, LitExpr<?>> getValueVisitor() {
		if(arithmetic == ArithmeticType.bitvector) return ValueVisitor.instance;
		else return hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer.ValueVisitor.instance;
	}
}