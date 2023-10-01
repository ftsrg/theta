package hu.bme.mit.theta.core.type.enumtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public final class EnumNeqExpr extends NeqExpr<EnumType> {

	private static final int HASH_SEED = 7212;
	private static final String OPERATOR_LABEL = "!=";

	private EnumNeqExpr(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		super(leftOp, rightOp);
	}
	public static EnumNeqExpr of(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		return new EnumNeqExpr(leftOp, rightOp);
	}

	@Override
	public BinaryExpr<EnumType, BoolType> with(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return EnumNeqExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public BinaryExpr<EnumType, BoolType> withLeftOp(Expr<EnumType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BinaryExpr<EnumType, BoolType> withRightOp(Expr<EnumType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(Valuation val) {
		return null;
	}
}
