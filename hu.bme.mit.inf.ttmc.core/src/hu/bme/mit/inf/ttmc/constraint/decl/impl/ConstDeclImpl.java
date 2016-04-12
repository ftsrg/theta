package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.DeclVisitor;

final class ConstDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType, ConstDecl<DeclType>>
		implements ConstDecl<DeclType> {

	private static final int HASH_SEED = 5351;
	private static final String DECL_LABEL = "Const";

	private volatile ConstRefExpr<DeclType> ref;

	ConstDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public ConstRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = Exprs.Ref(this);
		}

		return ref;
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getDeclLabel() {
		return DECL_LABEL;
	}

}
