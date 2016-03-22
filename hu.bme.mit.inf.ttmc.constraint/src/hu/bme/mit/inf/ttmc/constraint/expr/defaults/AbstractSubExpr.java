package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.TypeUtils;

public abstract class AbstractSubExpr<ExprType extends ClosedUnderSub>
		extends AbstractBinaryExpr<ExprType, ExprType, ExprType> implements SubExpr<ExprType> {

	private static final int HASH_SEED = 101;

	private static final String OPERATOR = "Sub";

	private final ConstraintManager manager;

	public AbstractSubExpr(final ConstraintManager manager, final Expr<? extends ExprType> leftOp,
			final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
		this.manager = manager;
	}

	@Override
	public final ExprType getType() {
		final ExprType leftType = getLeftOp().getType();
		final ExprType rightType = getRightOp().getType();
		final Optional<ExprType> joinResult = TypeUtils.join(leftType, rightType);
		final ExprType result = joinResult.get();
		return result;
	}

	@Override
	public final SubExpr<ExprType> withOps(final Expr<? extends ExprType> leftOp,
			final Expr<? extends ExprType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return manager.getExprFactory().Sub(leftOp, rightOp);
		}
	}

	@Override
	public final SubExpr<ExprType> withLeftOp(final Expr<? extends ExprType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final SubExpr<ExprType> withRightOp(final Expr<? extends ExprType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof SubExpr<?>) {
			final SubExpr<?> that = (SubExpr<?>) obj;
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
		return OPERATOR;
	}

}
