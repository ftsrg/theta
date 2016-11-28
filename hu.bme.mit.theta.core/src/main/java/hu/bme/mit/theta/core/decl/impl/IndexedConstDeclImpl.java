package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.IndexedConstRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

final class IndexedConstDeclImpl<DeclType extends Type> implements IndexedConstDecl<DeclType> {

	private static final String NAME_FORMAT = "_%s_%d";
	private static final String DECL_LABEL = "Const";
	private static final int HASH_SEED = 4603;

	private final VarDecl<DeclType> varDecl;
	private final int index;
	private final String name;
	private final IndexedConstRefExpr<DeclType> ref;

	private volatile int hashCode = 0;

	IndexedConstDeclImpl(final VarDecl<DeclType> varDecl, final int index) {
		checkNotNull(varDecl);
		checkArgument(index >= 0);

		this.varDecl = varDecl;
		this.index = index;
		name = String.format(NAME_FORMAT, varDecl.getName(), index);
		ref = new IndexedConstRefExprImpl<>(this);
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public DeclType getType() {
		return varDecl.getType();
	}

	@Override
	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	@Override
	public int getIndex() {
		return index;
	}

	@Override
	public IndexedConstRefExpr<DeclType> getRef() {
		return ref;
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + varDecl.hashCode();
			result = 31 * result + index;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(DECL_LABEL).add(varDecl.getName()).add(index).toString();
	}

}
