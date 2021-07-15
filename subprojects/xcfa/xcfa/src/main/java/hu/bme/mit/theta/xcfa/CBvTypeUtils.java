package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;
import hu.bme.mit.theta.xcfa.transformation.c.types.CTypeFactory;
import hu.bme.mit.theta.xcfa.transformation.c.types.NamedType;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.ArchitectureConfig.architecture;

/**
 * Note: char isn't an integer type in C, but we'll handle it here as well, as it isn't a floating point type
 */
public class CBvTypeUtils {
	// public static ArchitectureType architecture = ArchitectureType.ILP32;
	public static boolean addModulo = true;
	public static boolean signedOverflow = false;

	/**
	 * Creates assumptions based on the type of var about min and max values.
	 * Should be added after havoc statements.
	 * Cannot be turned off, as that can cause false positive cases.
	 * @param var the variable we make assumptions about
	 * @return two assumptions, one stating that the var has a value over the min value and another stating, that it is under it's max value
	 */
	public static AssumeStmt createWraparoundAssumptions(VarDecl<?> var) {
		NamedType type = CBvTypeUtils.getcTypeMetadata(var.getRef());
		AssumeStmt assume;
		AndExpr and;
		int bitWidth = architecture.getBitWidth(type.getNamedType());
		if(type.isSigned()) {
			BigInteger max = BigInteger.valueOf(2).pow(bitWidth-1).subtract(BigInteger.valueOf(1));
			BigInteger min = BigInteger.valueOf(2).pow(bitWidth-1);
			BvSLeqExpr leq = BvSLeqExpr.of(cast(var.getRef(), BvType.of(bitWidth)), BvUtils.bigIntegerToSignedBvLitExpr(max, bitWidth));
			BvSGeqExpr geq = BvSGeqExpr.of(cast(var.getRef(), BvType.of(bitWidth)), BvUtils.bigIntegerToSignedBvLitExpr(min, bitWidth));
			and = AndExpr.of(List.of(leq, geq));
		} else {
			BigInteger max = BigInteger.valueOf(2).pow(bitWidth).subtract(BigInteger.valueOf(1));
			BvULeqExpr leq = BvULeqExpr.of(cast(var.getRef(), BvType.of(bitWidth)), BvUtils.bigIntegerToSignedBvLitExpr(max, bitWidth));
			BvUGeqExpr geq = BvUGeqExpr.of(cast(var.getRef(), BvType.of(bitWidth)), BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.valueOf(0), bitWidth));
			and = AndExpr.of(List.of(leq, geq));
		}
		assume = AssumeStmt.of(and);
		return assume;
	}

	public static NamedType getcTypeMetadata(Object o) {
		Optional<Object> cTypeOptional = XcfaMetadata.getMetadataValue(o,"cType");
		if(cTypeOptional.isPresent() && cTypeOptional.get() instanceof CType) {
			CType cType = (CType) cTypeOptional.get();
			checkState(cType instanceof NamedType);
			return (NamedType) cType;
		} else return null;
	}

	/**
	 * Expressions (that are not variables) should have a type based on their operands
	 * Deducing this type follows the logic given below (based on the C11 standard):
	 *
	 * 1. Base types: unsigned/signed char/short/int/long/long long
	 * Note: signed int and int are the same BUT the signedness of char is implementation defined!
	 * (so there are three "chars": unsigned char, signed char and char)
	 * Solution: we output a warning (not in this function) if there is a char without explicit signedness, but
	 * by default we will handle it as a signed char.
	 *
	 * 2. Integer promotions
	 * "If an int can represent all values of the original type (as restricted by the width, for a
	 * bit-field), the value is converted to an int; otherwise, it is converted to an unsigned
	 * int. These are called the integer promotions.) All other types are unchanged by the
	 * integer promotions.
	 * The integer promotions preserve value including sign."
	 *
	 * 3. Usual arithmetic conversions
	 * "the integer promotions are performed on both operands. Then the
	 * following rules are applied to the promoted operands:
	 * 	If both operands have the same type, then no further conversion is needed.
	 * Otherwise, if both operands have signed integer types or both have unsigned
	 * integer types, the operand with the type of lesser integer conversion rank is
	 * converted to the type of the operand with greater rank.
	 *
	 * 	Otherwise, if the operand that has unsigned integer type has rank greater or
	 * equal to the rank of the type of the other operand, then the operand with
	 * signed integer type is converted to the type of the operand with unsigned
	 * integer type.
	 *
	 * 	Otherwise, if the type of the operand with signed integer type can represent
	 * all of the values of the type of the operand with unsigned integer type, then
	 * the operand with unsigned integer type is converted to the type of the
	 * operand with signed integer type.
	 *
	 * 	Otherwise, both operands are converted to the unsigned integer type
	 * corresponding to the type of the operand with signed integer type."
	 *
	 * 4. volatility and other attributes
	 * - an expression is volatile if there is at least one volatile variable in it
	 * - an expression cannot be atomic or extern
	 *
	 * Warning note: when deducing type, we assume an ILP32 or an LP64 arch
	 * (e.g. conversion rules would get more complex, if an int isn't at least twice as big as a short)
	 *
	 * 5. Floating point types
	 * TODO
	 *
	 * @param namedTypes list of the types of the operands in the expression
	 * @return the deduced type of the expression
	 */
	public static NamedType deduceType(List<NamedType> namedTypes) {
		// a few checks
		checkState(!namedTypes.isEmpty());
		for (NamedType type : namedTypes) {
			// non-supported:
			checkState(type.getPointerLevel()==0);

			// just to make sure, that we don't get any unsupported types here
			if(!(type.getNamedType().contains("int") || type.getNamedType().contains("char"))) {
				throw new RuntimeException("NamedType should contains int or char, instead it is: " + type.getNamedType());
			}
		}

		// deduction
		NamedType deducedType = namedTypes.get(0);
		for (int i = 1; i < namedTypes.size(); i++) {
			deducedType = deduceTypeBinary(deducedType, namedTypes.get(i));
		}
		return deducedType;
	}

	/**
	 * Type deduction of unary expressions
	 * @return a copy of the type, promoted to integer
	 */
	public static NamedType deduceType(NamedType type) {
		NamedType typeCopy = (NamedType) type.copyOf();
		promoteToInteger(typeCopy);
		return typeCopy;
	}

	/**
	 * The usual arithmetic conversions and other implicit conversion rules of the C standard are
	 * given for two operands, so the straightforward way of implementation is pairwise deduction.
	 * conversion rules: {@link #deduceType(List)}  }
	 *
	 * @param typeA First operand type
	 * @param typeB Second operand type
	 * @return the resulting type, which is not necessarily typeA or typeB
	 */
	static private NamedType deduceTypeBinary(NamedType typeA, NamedType typeB) {
		NamedType resultType = CTypeFactory.NamedType("int");
		if(typeA.isVolatile() || typeB.isVolatile()) {
			resultType.setVolatile(true);
		}
		resultType.setAtomic(false);
		resultType.setExtern(false);

		// integer promotion
		NamedType typeACopy = promoteToInteger(typeA);
		NamedType typeBCopy = promoteToInteger(typeB);

		// usual arithmetic conversions
		// same types
		if(typeACopy.isLongLong() == typeBCopy.isLongLong() &&
				typeACopy.isLong() == typeBCopy.isLong() &&
				typeACopy.isSigned() == typeBCopy.isSigned()) {
			copyIntType(typeACopy, resultType);
		}
		// both signed or both unsigned -> rank
		else if(typeACopy.isSigned() == typeBCopy.isSigned()) {
			if(rankLessThan(typeACopy, typeBCopy)) {
				copyIntType(typeBCopy, resultType);
			} else copyIntType(typeACopy, resultType);
		} else {
			NamedType unsignedType = typeA.isSigned() ? typeBCopy : typeACopy;
			NamedType signedType = typeA.isSigned() ? typeACopy : typeBCopy;

			// unsigned has >= rank -> unsigned type
			if(rankLessThan(signedType, unsignedType)) {
				copyIntType(unsignedType, resultType);
			} else if(architecture.getBitWidth(signedType.getNamedType()) >= 2*architecture.getBitWidth(unsignedType.getNamedType())) {
				// unsigned has < rank & signed is at least twice the size -> signed type
				copyIntType(signedType, resultType);
			} else {
				// unsigned has < rank & signed is less than twice the size -> unsigned version of signed type
				copyIntType(signedType, resultType);
				resultType.setSigned(false);
			}
		}
		return resultType;
	}

	/**
	 * Copies the short, long, longlong and signedness attributes and nothing else
	 *
	 * @param src copy to
	 * @param dest copy from
	 */
	static private void copyIntType(NamedType src, NamedType dest) {
		dest.setShort(src.isShort());
		dest.setLong(src.isLong());
		dest.setLongLong(src.isLongLong());
		dest.setSigned(src.isSigned());
	}

	static private boolean rankLessThan(NamedType typeA, NamedType typeB) {
		if(typeA.getNamedType().contains("char")) {
			if(typeB.getNamedType().contains("char")) { // both are chars
				return false;
			} else return true; // only A is a char
		} else if(typeB.getNamedType().contains("char")) { // only B is a char
			return true;
		} else { // both are ints
			if (typeB.isLongLong() && !typeA.isLongLong()) {
				return true;
			} else if (typeB.isLong() && !typeA.isLongLong() && !typeA.isLong()) {
				return true;
			} else if (!typeB.isShort() && typeA.isShort()) {
				return true;
			} else return false;
		}
	}

	/**
	 * Integer promotions
	 * 	 "If an int can represent all values of the original type (as restricted by the width, for a
	 * 	 bit-field), the value is converted to an int; otherwise, it is converted to an unsigned
	 * 	 int. These are called the integer promotions.) All other types are unchanged by the
	 * 	 integer promotions.
	 * 	 The integer promotions preserve value including sign."
	 *
	 * Assumption: we are in an architecture, where a signed integer can represent all values of both
	 * signed and unsigned shorts or chars (ILP32 and LP64 are such)
	 *
	 * @param type type to promote
	 * @return promoted type, it must be an int and cannot be short
	 */
	static private NamedType promoteToInteger(NamedType type) {
		// integer promotion
		NamedType typeCopy = null;
		if(type.getNamedType().contains("char")) {
			typeCopy = CTypeFactory.NamedType("int");
			typeCopy.setSigned(true);
			typeCopy.setLongLong(false);
			typeCopy.setLong(false);
		} else if(type.isShort()) {
			typeCopy = (NamedType) type.copyOf();
			typeCopy.setShort(false);
			typeCopy.setSigned(true);
		} else {
			typeCopy = (NamedType) type.copyOf();
		}
		return typeCopy;
	}

	/**
	 *
	 * @param innerExpr to wrap around, it must have a cType XCFA Metadata
	 * @return a modulo expression, wrapped around innerExpr
	 */
	public static Expr<BvType> addOverflowWraparound(Expr<BvType> innerExpr) {
		NamedType namedType = getcTypeMetadata(innerExpr);
		Integer namedTypeBitWidth = architecture.getBitWidth(namedType.getNamedType());
		if(addModulo) {
			if(!namedType.isSigned()) {
				BvURemExpr urem = BvURemExpr.of(innerExpr, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(2).pow(namedTypeBitWidth), namedTypeBitWidth));
				XcfaMetadata.create(urem, "cType", namedType);
				return urem;
			} else {
				if(signedOverflow) {
					System.err.println("WARNING: Possibility of signed overflow of the expression " + innerExpr + " (with wraparound, but this is undefined behaviour)");
					// complex mod: ( (signed expr + half width) mod 2*signedTypeMax ) - half width
					BvSRemExpr srem = BvSRemExpr.of(innerExpr, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.valueOf(2).pow(namedTypeBitWidth), namedTypeBitWidth));
					XcfaMetadata.create(srem, "cType", namedType);
					return srem;
				} else {
					System.err.println("WARNING: Possibility of signed overflow of the expression " + innerExpr + " (and thus undefined behaviour and false positives)");
					return innerExpr;
				}
			}
		} else {
			return innerExpr;
		}

	}

	public static Expr<BvType> explicitCast(NamedType namedType, Expr<BvType> exprToCast) {
		checkNotNull(namedType);
		checkNotNull(exprToCast);
		Expr<BvType> ret;
		int namedTypeBitWidth = architecture.getBitWidth(namedType.getNamedType());

		NamedType exprType = getcTypeMetadata(exprToCast);
		int exprTypeBitWidth = architecture.getBitWidth(exprType.getNamedType());

		// types aren't necessarily the same, but signedness and width is the same
		// so no arithmetic addition is needed, but the new expression should have the given type as a metadata
		if(namedType.isSigned() == exprType.isSigned() &&
			namedTypeBitWidth == exprTypeBitWidth) {
			ret = cast(AbstractExprs.Pos(exprToCast), BvType.of(namedTypeBitWidth));
			XcfaMetadata.create(ret, "cType", namedType);
			return ret;
		}

		//	typeToCastTo    Expr        What to do
		//	unsigned        unsigned    easy, check widths, add mod if needed
		//	signed          signed      check widths, add complex mod
		//	unsigned        signed      add mod, even if Expr is smaller (to filter out neg numbers)
		//	signed          unsigned    check widths, add complex mod
		if(namedType.isSigned() && namedTypeBitWidth < exprTypeBitWidth) {
			// complex mod: ( (signed expr + half width) mod 2*signedTypeMax ) - half width
			BvSRemExpr srem = BvSRemExpr.of(exprToCast, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.valueOf(2).pow(namedTypeBitWidth), namedTypeBitWidth));
			XcfaMetadata.create(srem, "cType", namedType);
			return srem;
		} else if(exprType.isSigned() || namedTypeBitWidth < exprTypeBitWidth) {
			BvURemExpr urem = BvURemExpr.of(exprToCast, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(2).pow(namedTypeBitWidth), namedTypeBitWidth));
			XcfaMetadata.create(urem, "cType", namedType);
			return urem;
		} else { // TODO BV special case: when it becomes longer
			return exprToCast;
		}
	}

	/** The semantics of this function differ from its integer counterpart - it must be used much more often
	 *  it changes not just the cType metadata, but the width of the BvTypes as well
	 *  so various operations can be executed on them
	 */
	public static Tuple2<Expr<BvType>, Expr<BvType>> castToCommonType(Expr<BvType> exprA, Expr<BvType> exprB) {
		checkNotNull(exprA);
		checkNotNull(exprB);
		NamedType commonType = CBvTypeUtils.deduceType(List.of(
				CBvTypeUtils.getcTypeMetadata(exprA),
				CBvTypeUtils.getcTypeMetadata(exprB)));
		Expr<BvType> castExprA = CBvTypeUtils.explicitCast(commonType, exprA);
		Expr<BvType> castExprB = CBvTypeUtils.explicitCast(commonType, exprB);
		return Tuple2.of(castExprA, castExprB);
	}

	public static Expr<BvType> getBvValueOfType(NamedType cType, int value) {
		int width = architecture.getBitWidth(cType.getNamedType());
		if(cType.isSigned()) {
			return BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.valueOf(value), width);
		} else {
			return BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(value), width);
		}
	}

	public static int getBitWidth(NamedType cType) {
		return architecture.getBitWidth(cType.getNamedType());
	}

	// TODO floating point types (float, double, long double)
}
