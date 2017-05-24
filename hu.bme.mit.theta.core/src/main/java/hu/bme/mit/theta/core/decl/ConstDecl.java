package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.DeclVisitor;

public abstract class ConstDecl<DeclType extends Type> extends Decl<DeclType> {
	private static final String DECL_LABEL = "Const";

	ConstDecl() {
	}

	@Override
	public final <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(DECL_LABEL).add(getName()).add(getType()).toString();
	}

}
