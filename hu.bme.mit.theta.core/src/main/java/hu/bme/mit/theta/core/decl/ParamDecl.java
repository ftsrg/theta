package hu.bme.mit.theta.core.decl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public final class ParamDecl<DeclType extends Type> extends Decl<DeclType> {

	private static final String DECL_LABEL = "Param";

	private final String name;
	private final DeclType type;

	ParamDecl(final String name, final DeclType type) {
		this.name = checkNotNull(name);
		this.type = checkNotNull(type);
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public DeclType getType() {
		return type;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(DECL_LABEL).add(name).add(type).toString();
	}
}
