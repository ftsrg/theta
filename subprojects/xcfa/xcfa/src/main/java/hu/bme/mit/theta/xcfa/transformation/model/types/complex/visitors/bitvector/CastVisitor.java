package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.Unsigned;
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
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CLongDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CReal;

import java.math.BigInteger;
import java.util.List;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
	public static final CastVisitor instance = new CastVisitor();

	private Expr<? extends Type> handleSignedConversion(CInteger type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CReal) throw new UnsupportedOperationException("Reals and integers are not yet compatible!");
		else if (that instanceof CInteger) {
			if(that.width() < type.width()) {
				if(that instanceof Unsigned) param = BvExprs.Add(List.of(BvExprs.Neg(cast(param, BvType.of(that.width()))), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, that.width())));
				return BvExprs.SExt(cast(param, BvType.of(that.width())), BvType.of(type.width()));
			} else if (that.width() > type.width()) {
				return BvExprs.Extract(cast(param, BvType.of(that.width())), Int(type.width()-1), Int(0));
			} else return param;
		} else {
			throw new IllegalStateException("Compound types are not directly supported!");
		}
	}

	private Expr<? extends Type> handleUnsignedConversion(CInteger type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CReal) throw new UnsupportedOperationException("Reals and integers are not yet compatible!");
		else if (that instanceof CInteger) {
			if(that.width() < type.width()) {
				if(that instanceof Signed) param = BvExprs.Add(List.of(BvExprs.Neg(cast(param, BvType.of(that.width()))), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, that.width())));
				return BvExprs.SExt(cast(param, BvType.of(that.width())), BvType.of(type.width()));
			} else if (that.width() > type.width()) {
				return BvExprs.Extract(cast(param, BvType.of(that.width())), Int(type.width()-1), Int(0));
			} else return param;
		} else {
			throw new IllegalStateException("Compound types are not directly supported!");
		}
	}

	@Override
	public Expr<?> visit(CSignedShort type, Expr<?> param) {
		return handleSignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CUnsignedShort type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CSignedLongLong type, Expr<?> param) {
		return handleSignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CUnsignedLongLong type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CUnsignedLong type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CSignedLong type, Expr<?> param) {
		return handleSignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CSignedInt type, Expr<?> param) {
		return handleSignedConversion(type, param);

	}

	@Override
	public Expr<?> visit(CUnsignedInt type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CSignedChar type, Expr<?> param) {
		return handleSignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CUnsignedChar type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CBool type, Expr<?> param) {
		return handleUnsignedConversion(type, param);
	}

	@Override
	public Expr<?> visit(CVoid type, Expr<?> param) {
		return param;
	}

	@Override
	public Expr<?> visit(CDouble type, Expr<?> param) {
		return param;
	}

	@Override
	public Expr<?> visit(CFloat type, Expr<?> param) {
		return param;
	}

	@Override
	public Expr<?> visit(CLongDouble type, Expr<?> param) {
		return param;
	}
}
