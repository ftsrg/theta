package hu.bme.mit.inf.ttmc.core.decl.impl;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;

final class ParamDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType, ParamDecl<DeclType>>
		implements ParamDecl<DeclType> {

	private static final int HASH_SEED = 6949;
	private static final String DECL_LABEL = "Param";

	private final ParamRefExpr<DeclType> ref;

	ParamDeclImpl(final String name, final DeclType type) {
		super(name, type);
		ref = new ParamRefExprImpl<>(this);
	}

	@Override
	public ParamRefExpr<DeclType> getRef() {
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
