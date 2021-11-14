package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort.CUnsignedShort;

import java.math.BigInteger;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
	public static final CastVisitor instance = new CastVisitor();


	private IteExpr<?> handleUnsignedSameSize(CInteger type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof Unsigned && that.width() == type.width()) {
			IntLitExpr maxSigned = Int(BigInteger.TWO.pow(type.width() - 1));
			IntLitExpr maxUnsigned = Int(BigInteger.TWO.pow(type.width()));
			return Ite(Geq(param, maxSigned), Sub(param, maxUnsigned), param);
		}
		return null;
	}

	@Override
	public Expr<?> visit(Fitsall type, Expr<?> param) {
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("fitsall");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CSignedShort type, Expr<?> param) {
		IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
		if (sameSizeExpr != null) return sameSizeExpr;
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("short");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Mod(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
		IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
		if (sameSizeExpr != null) return sameSizeExpr;
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("longlong");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Mod(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Mod(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedLong type, Expr<?> param) {
		IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
		if (sameSizeExpr != null) return sameSizeExpr;
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("long");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CSignedInt type, Expr<?> param) {
		IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
		if (sameSizeExpr != null) return sameSizeExpr;
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}


	@Override
	public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("int");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Mod(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CSignedChar type, Expr<?> param) {
		IteExpr<?> sameSizeExpr = handleUnsignedSameSize(type, param);
		if (sameSizeExpr != null) return sameSizeExpr;
		if(true) return Pos(param);
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		BigInteger minValue = BigInteger.TWO.pow(width-1).negate();
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Sub(Mod(Add(param, Int(minValue)), Int(upperLimit)), Int(minValue));
	}

	@Override
	public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
		int width = ArchitectureConfig.architecture.getBitWidth("char");
		BigInteger upperLimit = BigInteger.TWO.pow(width);
		return Mod(param, Int(upperLimit));
	}

	@Override
	public Expr<?> visit(CBool type, Expr<?> param) {
		return Ite(Eq(param, Int(0)), Int(0), Int(1));
	}

	@Override
	public Expr<?> visit(CVoid type, Expr<?> param) {
		return param.withOps(param.getOps());
	}

	@Override
	public Expr<?> visit(CArray type, Expr<?> param) {
		checkState(CComplexType.getType(param) instanceof CArray, "Only arrays can be used in place of arrays!");
		return param.withOps(param.getOps());
	}

	@Override
	public Expr<?> visit(CPointer type, Expr<?> param) {
		if(CComplexType.getType(param) instanceof CPointer) return param.withOps(param.getOps());
		return visit((CUnsignedLong) CComplexType.getUnsignedLong(), param);
	}
}
