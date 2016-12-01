package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

final class VarDeclImpl<DeclType extends Type> extends AbstractDecl<DeclType> implements VarDecl<DeclType> {

	private static final int HASH_SEED = 3761;
	private static final String DECL_LABEL = "Var";

	private final VarRefExpr<DeclType> ref;
	private final Map<Integer, IndexedConstDecl<DeclType>> indexToConst;

	VarDeclImpl(final String name, final DeclType type) {
		super(name, type);
		ref = new VarRefExprImpl<>(this);
		indexToConst = new HashMap<>();
	}

	@Override
	public VarRefExpr<DeclType> getRef() {
		return ref;
	}

	@Override
	public IndexedConstDecl<DeclType> getConstDecl(final int index) {
		checkArgument(index >= 0);
		IndexedConstDecl<DeclType> constDecl = indexToConst.get(index);
		if (constDecl == null) {
			constDecl = new IndexedConstDeclImpl<>(this, index);
			indexToConst.put(index, constDecl);
		}
		return constDecl;
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
