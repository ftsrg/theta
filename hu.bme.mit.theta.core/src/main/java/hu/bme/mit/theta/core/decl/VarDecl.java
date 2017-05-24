package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public final class VarDecl<DeclType extends Type> extends Decl<DeclType> {
	private static final String DECL_LABEL = "Var";

	private final String name;
	private final DeclType type;
	private final Map<Integer, IndexedConstDecl<DeclType>> indexToConst;

	VarDecl(final String name, final DeclType type) {
		this.name = checkNotNull(name);
		this.type = checkNotNull(type);
		indexToConst = new HashMap<>();
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public DeclType getType() {
		return type;
	}

	public IndexedConstDecl<DeclType> getConstDecl(final int index) {
		checkArgument(index >= 0);
		IndexedConstDecl<DeclType> constDecl = indexToConst.get(index);
		if (constDecl == null) {
			constDecl = new IndexedConstDecl<>(this, index);
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
	public String toString() {
		return ObjectUtils.toStringBuilder(DECL_LABEL).add(name).add(type).toString();
	}

}
