package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.DeclVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.VarRefExprImpl;

public final class VarDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType, VarDecl<DeclType>>
		implements VarDecl<DeclType> {

	private static final int HASH_SEED = 3761;

	private static final String DECL_LABEL = "Var";

	protected volatile VarRefExpr<DeclType> ref;

	public VarDeclImpl(final String name, final DeclType type) {
		super(name, type);
	}

	@Override
	public VarRefExpr<DeclType> getRef() {
		if (ref == null) {
			ref = new VarRefExprImpl<>(this);
		}

		return ref;
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
