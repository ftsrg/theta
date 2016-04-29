package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import hu.bme.mit.inf.ttmc.core.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

final class VarDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements VarDecl<DeclType> {

	private static final int HASH_SEED = 3761;

	private static final String DECL_LABEL = "Var";

	VarDeclImpl(final String name, final DeclType type) {
		super(name, type);
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
