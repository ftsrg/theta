package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

public class XorExpr extends NeqExpr<BoolType> {

	private static final int HASH_SEED = 937;

	private static final String OPERATOR_LABEL = "Xor";

	XorExpr(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Valuation val) {
		final BoolLitExpr leftOpVal = (BoolLitExpr) getLeftOp().eval(val);
		final BoolLitExpr rightOpVal = (BoolLitExpr) getRightOp().eval(val);
		return Bool(leftOpVal.getValue() != rightOpVal.getValue());
	}

	@Override
	public BinaryExpr<BoolType, BoolType> with(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new XorExpr(leftOp, rightOp);
		}
	}

	@Override
	public BinaryExpr<BoolType, BoolType> withLeftOp(final Expr<BoolType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BinaryExpr<BoolType, BoolType> withRightOp(final Expr<BoolType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
