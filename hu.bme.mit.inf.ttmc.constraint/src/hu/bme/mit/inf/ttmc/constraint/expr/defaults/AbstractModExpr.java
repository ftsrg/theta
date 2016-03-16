package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractModExpr extends AbstractBinaryExpr<IntType, IntType, IntType> implements ModExpr {

	private static final String OPERATOR = "Mod";

	public AbstractModExpr(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public ModExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public ModExpr withLeftOp(final Expr<? extends IntType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public ModExpr withRightOp(final Expr<? extends IntType> rightOp) {
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
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 109;
	}
}