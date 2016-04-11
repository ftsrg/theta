package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public final class ConstRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, ConstDecl<DeclType>>
		implements ConstRefExpr<DeclType> {

	private static final int HASH_SEED = 167;

	@SuppressWarnings("unused")
	private final ConstraintManager manager;

	public ConstRefExprImpl(final ConstraintManager manager, final ConstDecl<DeclType> constDecl) {
		super(constDecl);
		this.manager = manager;
	}

	@Override
	public DeclType getType() {
		return getDecl().getType();
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
