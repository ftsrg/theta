package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import hu.bme.mit.inf.ttmc.core.decl.impl.AbstractRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;

final class VarRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, VarDecl<DeclType>>
		implements VarRefExpr<DeclType> {

	private static final int HASH_SEED = 313;

	VarRefExprImpl(final VarDecl<DeclType> varDecl) {
		super(varDecl);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof VarRefExprVisitor<?, ?>) {
			final VarRefExprVisitor<? super P, ? extends R> sVisitor = (VarRefExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof VarRefExpr<?>) {
			final VarRefExpr<?> that = (VarRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	protected final int getHashSeed() {
		return HASH_SEED;
	}

}
