package hu.bme.mit.inf.ttmc.constraint.type.impl;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

final class BoolTypeImpl implements BoolType {

	private static final int HASH_SEED = 754364;

	private static final String TYPE_LABEL = "Bool";

	public BoolTypeImpl() {
	}

	@Override
	public Expr<BoolType> getAny() {
		return Exprs.False();
	}

	@Override
	public boolean isLeq(final Type type) {
		return this.equals(type);
	}

	@Override
	public Optional<BoolType> meet(final Type type) {
		if (type.isLeq(this)) {
			assert type instanceof BoolType;
			final BoolType that = (BoolType) type;
			return Optional.of(that);
		} else {
			assert !this.isLeq(type);
			return Optional.empty();
		}
	}

	@Override
	public Optional<BoolType> join(final Type type) {
		if (type.isLeq(this)) {
			return Optional.of(this);
		} else {
			assert !this.isLeq(type);
			return Optional.empty();
		}
	}

	@Override
	public <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof BoolTypeImpl;
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

}
