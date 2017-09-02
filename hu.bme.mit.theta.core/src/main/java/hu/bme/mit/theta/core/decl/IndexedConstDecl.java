package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.type.Type;

public final class IndexedConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {
	private static final String NAME_FORMAT = "_%s:%d";

	private final VarDecl<DeclType> varDecl;
	private final int index;

	IndexedConstDecl(final VarDecl<DeclType> varDecl, final int index) {
		checkNotNull(varDecl);
		checkArgument(index >= 0);
		this.varDecl = varDecl;
		this.index = index;
	}

	@Override
	public String getName() {
		return String.format(NAME_FORMAT, varDecl.getName(), index);
	}

	@Override
	public DeclType getType() {
		return varDecl.getType();
	}

	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	public int getIndex() {
		return index;
	}

}
