package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Type;

public abstract class ConstDecl<DeclType extends Type> extends AbstractDecl<DeclType> {
	private static final String DECL_LABEL = "Const";

	ConstDecl() {
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(DECL_LABEL).add(getName()).add(getType()).toString();
	}

}
