package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpExprs;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Fitsall;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
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
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CReal;

import java.math.BigInteger;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.ToFp;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CastVisitor extends CComplexType.CComplexTypeVisitor<Expr<?>, Expr<?>> {
	public static final CastVisitor instance = new CastVisitor();

	private Expr<? extends Type> handleSignedConversion(CInteger type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CPointer) that = CComplexType.getUnsignedLong();
		if(that instanceof CReal) {
			//noinspection unchecked
			return FpExprs.ToBv(FpRoundingMode.RTZ, (Expr<FpType>) param, type.width(), true);
		}
		else if (that instanceof CInteger) {
			if(that.width() < type.width()) {
				if(that instanceof Unsigned) return BvExprs.ZExt(cast(param, BvType.of(that.width())), BvType.of(type.width(),true));
				return BvExprs.SExt(cast(param, BvType.of(that.width())), BvType.of(type.width(),true));
			} else if (that.width() > type.width()) {
				return BvExprs.Extract(cast(param, BvType.of(that.width())), Int(0), Int(type.width()));
			} else return param.withOps(param.getOps());
		} else {
			throw new IllegalStateException("Compound types are not directly supported!");
		}
	}

	private Expr<? extends Type> handleUnsignedConversion(CInteger type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CPointer) that = CComplexType.getUnsignedLong();
		if(that instanceof CReal) {
			//noinspection unchecked
			return FpExprs.ToBv(FpRoundingMode.RTZ, (Expr<FpType>) param, type.width(), false);
		}
		else if (that instanceof CInteger) {
			if(that.width() < type.width()) {
				if(that instanceof Signed) param = BvExprs.Add(List.of(BvExprs.Neg(cast(param, BvType.of(that.width()))), BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, that.width())));
				return BvExprs.ZExt(cast(param, BvType.of(that.width())), BvType.of(type.width(), false));
			} else if (that.width() > type.width()) {
				return BvExprs.Extract(cast(param, BvType.of(that.width())), Int(0), Int(type.width()));
			} else return param.withOps(param.getOps());
		} else {
			throw new IllegalStateException("Compound types are not directly supported!");
		}
	}

	private Expr<FpType> handleFp(CReal type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CReal) {
			FpType fpType = (FpType) type.getSmtType();
			//noinspection unchecked
			return ToFp(FpRoundingMode.RTZ, (Expr<FpType>) param, fpType.getExponent(), fpType.getSignificand());
		} else if (that instanceof CInteger) {
			boolean signed = that instanceof Signed;
			//noinspection unchecked
			return FromBv(FpRoundingMode.RTZ, (Expr<BvType>) param, (FpType) type.getSmtType(), signed);
		} else throw new UnsupportedOperationException("Bad type!");
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
	public Expr<?> visit(Fitsall type, Expr<?> param) {
		return handleSignedConversion(type, param);
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
		return param.withOps(param.getOps());
	}

	@Override
	public Expr<?> visit(CDouble type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CDouble)
			return param.withOps(param.getOps());
		return handleFp(type, param);
	}

	@Override
	public Expr<?> visit(CFloat type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CFloat)
			return param.withOps(param.getOps());
		return handleFp(type, param);

	}

	@Override
	public Expr<?> visit(CLongDouble type, Expr<?> param) {
		CComplexType that = CComplexType.getType(param);
		if(that instanceof CLongDouble)
			return param.withOps(param.getOps());
		return handleFp(type, param);

	}

	@Override
	public Expr<?> visit(CArray type, Expr<?> param) {
		checkState(CComplexType.getType(param) instanceof CArray, "Only arrays can be used in place of arrays!");
		return param.withOps(param.getOps());
	}


	@Override
	public Expr<?> visit(CPointer type, Expr<?> param) {
		return handleUnsignedConversion((CInteger) CComplexType.getUnsignedLong(), param);
	}
}