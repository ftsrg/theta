package hu.bme.mit.theta.core.type.enumtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class EnumEqExpr extends EqExpr<EnumType> {

	private static final int HASH_SEED = 5326;
	private static final String OPERATOR_LABEL = "=";

	private EnumEqExpr(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		super(leftOp, rightOp);
	}

	public static EnumEqExpr of(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		return new EnumEqExpr(leftOp, rightOp);
	}

	@Override
	public BinaryExpr<EnumType, BoolType> with(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return EnumEqExpr.of(leftOp, rightOp);
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
		return EnumLitExpr.eq((EnumLitExpr) getLeftOp().eval(val), (EnumLitExpr) getRightOp().eval(val));
	}
}
