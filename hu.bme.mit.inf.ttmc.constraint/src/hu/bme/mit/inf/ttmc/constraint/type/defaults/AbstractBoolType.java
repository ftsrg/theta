package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public abstract class AbstractBoolType extends AbstractBaseType implements BoolType {

	private static final int HASH_SEED = 754364;

	private static final String TYPE_LABEL = "Bool";

	@Override
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		return HASH_SEED;
	}

	@Override
	public final boolean equals(final Object obj) {
		return (obj instanceof BoolType);
	}

	@Override
	public final String toString() {
		return TYPE_LABEL;
	}

}
