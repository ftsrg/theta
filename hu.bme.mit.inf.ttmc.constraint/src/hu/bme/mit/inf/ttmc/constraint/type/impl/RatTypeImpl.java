package hu.bme.mit.inf.ttmc.constraint.type.impl;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public final class RatTypeImpl implements RatType {

	private static final int HASH_SEED = 385863;

	private static final String TYPE_LABEL = "Rat";

	private final ConstraintManager manager;

	public RatTypeImpl(final ConstraintManager manager) {
		this.manager = manager;
	}

	@Override
	public Expr<RatType> getAny() {
		return manager.getExprFactory().Rat(0, 1);
	}

	@Override
	public boolean isLeq(final Type type) {
		return this.equals(type);
	}

	@Override
	public Optional<? extends RatType> meet(final Type type) {
		if (type.isLeq(this)) {
			assert type instanceof RatType;
			final RatType that = (RatType) type;
			return Optional.of(that);
		} else {
			assert !this.isLeq(type);
			return Optional.empty();
		}
	}

	@Override
	public Optional<RatType> join(final Type type) {
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
		return (obj instanceof RatTypeImpl);
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

}
