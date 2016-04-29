package hu.bme.mit.inf.ttmc.core.expr.impl;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

final class ParamRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, ParamDecl<DeclType>>
		implements ParamRefExpr<DeclType> {

	private static final int HASH_SEED = 919;

	ParamRefExprImpl(final ParamDecl<DeclType> paramDecl) {
		super(paramDecl);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ParamRefExpr<?>) {
			final ParamRefExpr<?> that = (ParamRefExpr<?>) obj;
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
