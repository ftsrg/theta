package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.*;

public class FpAbsExpr extends UnaryExpr<FpType, FpType> {
	private static final int HASH_SEED = 6666;
	private static final String OPERATOR_LABEL = "fpabs";

	private FpAbsExpr(final Expr<FpType> op) {
		super(op);
	}

	public static FpAbsExpr of(final Expr<FpType> op) {
		return new FpAbsExpr(castFp(op));
	}

	public static FpAbsExpr create(final Expr<?> op) {
		checkNotNull(op);
		return FpAbsExpr.of(castFp(op));
	}

	@Override
	public FpType getType() {
		return getOp().getType();
	}

	@Override
	public FpLitExpr eval(Valuation val) {
		final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
		if(opVal.getHidden()) {
			return opVal.neg();
		} else {
			return opVal;
		}
	}

	@Override
	public FpAbsExpr with(final Expr<FpType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpAbsExpr.of(op);
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
