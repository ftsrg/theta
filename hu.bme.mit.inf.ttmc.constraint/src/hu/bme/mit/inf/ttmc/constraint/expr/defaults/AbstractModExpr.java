package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractModExpr extends AbstractBinaryExpr<IntType, IntType, IntType> implements ModExpr {

	private static final int HASH_SEED = 109;

	private static final String OPERATOR_LABEL = "Mod";

	private final ConstraintManager manager;

	public AbstractModExpr(final ConstraintManager manager, final Expr<? extends IntType> leftOp,
			final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
		this.manager = manager;
	}

	@Override
	public final IntType getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final ModExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return manager.getExprFactory().Mod(leftOp, rightOp);
		}
	}

	@Override
	public final ModExpr withLeftOp(final Expr<? extends IntType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final ModExpr withRightOp(final Expr<? extends IntType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
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
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}