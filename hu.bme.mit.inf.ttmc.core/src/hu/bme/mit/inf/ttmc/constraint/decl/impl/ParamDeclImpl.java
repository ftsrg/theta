package hu.bme.mit.inf.ttmc.constraint.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.DeclVisitor;

final class ParamDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType, ParamDecl<DeclType>>
		implements ParamDecl<DeclType> {

	private static final int HASH_SEED = 6949;
	private static final String DECL_LABEL = "Param";

	private volatile ParamRefExpr<DeclType> ref;

	ParamDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public ParamRefExpr<DeclType> getRef() {
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
