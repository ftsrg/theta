package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public class ModExprImpl extends AbstractBinaryExpr<IntType, IntType, IntType> implements ModExpr {

	private static final String OPERATOR = "Mod";
	
	public ModExprImpl(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}
	
	@Override
	public ModExpr withOps(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new ModExprImpl(leftOp, rightOp);
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