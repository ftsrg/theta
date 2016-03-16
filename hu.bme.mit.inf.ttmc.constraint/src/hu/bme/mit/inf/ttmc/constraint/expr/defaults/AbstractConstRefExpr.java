package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractConstRefExpr<DeclType extends Type> extends AbstractRefExpr<DeclType, ConstDecl<DeclType>>
		implements ConstRefExpr<DeclType> {

	private static final int HASH_SEED = 167;

	public AbstractConstRefExpr(final ConstraintManager manager, final ConstDecl<DeclType> constDecl) {
		super(constDecl);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
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
	protected final int getHashSeed() {
		return HASH_SEED;
	}

}
