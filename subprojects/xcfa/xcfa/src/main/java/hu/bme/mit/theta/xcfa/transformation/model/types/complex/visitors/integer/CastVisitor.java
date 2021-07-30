package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CUnsignedShort;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Rem;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
	public static final CastVisitor instance = new CastVisitor();

	@Override
	public Expr<?> visit(CSignedShort type, Expr<?> param) {
		if(true) return param;
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Rem(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Rem(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
		if(true) return param;
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Rem(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Rem(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Rem(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedLong type, Expr<?> param) {
		if(true) return param;
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Rem(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CSignedInt type, Expr<?> param) {
		if(true) return param;
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Rem(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Rem(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedChar type, Expr<?> param) {
		if(true) return param;
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Rem(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Rem(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CBool type, Expr<?> param) {
		return Ite(Eq(param, Int(0)), Int(0), Int(1));
	}
}
