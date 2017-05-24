package hu.bme.mit.theta.core.decl.impl;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

final class ParamDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements ParamDecl<DeclType> {

	private static final int HASH_SEED = 6949;
	private static final String DECL_LABEL = "Param";

	private final RefExpr<DeclType> ref;

	ParamDeclImpl(final String name, final DeclType type) {
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
