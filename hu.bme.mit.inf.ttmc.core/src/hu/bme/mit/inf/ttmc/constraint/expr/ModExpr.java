package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public interface ModExpr extends BinaryExpr<IntType, IntType, IntType> {
	
	@Override
	public ModExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	public ModExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	public ModExpr withRightOp(final Expr<? extends IntType> rightOp);
}