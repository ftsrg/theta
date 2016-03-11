
package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractIffExpr extends AbstractBinaryExpr<BoolType, BoolType, BoolType>
		implements IffExpr {

	private static final String OPERATOR = "Iff";

	public AbstractIffExpr(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 67;
	}
	
	@Override
	public IffExpr withOps(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final IffExpr withLeftOp(final Expr<? extends BoolType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final IffExpr withRightOp(final Expr<? extends BoolType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
