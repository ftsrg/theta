package hu.bme.mit.inf.theta.core.decl.impl;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

final class ConstRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, ConstDecl<DeclType>>
		implements ConstRefExpr<DeclType> {

	private static final int HASH_SEED = 167;

	ConstRefExprImpl(final ConstDecl<DeclType> constDecl) {
		super(constDecl);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ConstRefExpr<?>) {
			final ConstRefExpr<?> that = (ConstRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

}
