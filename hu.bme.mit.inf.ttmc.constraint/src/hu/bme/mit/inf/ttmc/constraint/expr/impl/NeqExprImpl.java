package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public final class NeqExprImpl extends AbstractBinaryExpr<Type, Type, BoolType> implements NeqExpr {

	private static final int HASH_SEED = 113;

	private static final String OPERATOR_LABEL = "Neq";

	private final ConstraintManager manager;

	public NeqExprImpl(final ConstraintManager manager, final Expr<? extends Type> leftOp,
			final Expr<? extends Type> rightOp) {
		super(leftOp, rightOp);
		this.manager = manager;
	}

	@Override
	public BoolType getType() {
		return manager.getTypeFactory().Bool();
	}

	@Override
	public NeqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return manager.getExprFactory().Neq(leftOp, rightOp);
		}
	}

	@Override
	public NeqExpr withLeftOp(final Expr<? extends Type> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public NeqExpr withRightOp(final Expr<? extends Type> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ModExpr) {
			final ModExpr that = (ModExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
		} else {
			return false;
		}
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
