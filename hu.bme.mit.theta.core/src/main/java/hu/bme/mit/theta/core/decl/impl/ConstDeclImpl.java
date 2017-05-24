package hu.bme.mit.theta.core.decl.impl;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

final class ConstDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements ConstDecl<DeclType> {

	private static final int HASH_SEED = 5351;
	private static final String DECL_LABEL = "Const";

	private final RefExpr<DeclType> ref;

	ConstDeclImpl(final String name, final DeclType type) {
		super(name, type);
		ref = Exprs.Ref(this);
	}

	@Override
	public RefExpr<DeclType> getRef() {
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
