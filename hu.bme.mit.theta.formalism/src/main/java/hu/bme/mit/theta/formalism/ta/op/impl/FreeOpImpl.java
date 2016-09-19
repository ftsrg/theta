package hu.bme.mit.theta.formalism.ta.op.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Havoc;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.op.FreeOp;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

final class FreeOpImpl implements FreeOp {

	private static final int HASH_SEED = 2281;

	private final ClockDecl clock;

	private volatile int hashCode = 0;
	private volatile HavocStmt<RatType> stmt = null;

	FreeOpImpl(final ClockDecl clock) {
		this.clock = checkNotNull(clock);
	}

	@Override
	public ClockDecl getClock() {
		return clock;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of(clock);
	}

	@Override
	public HavocStmt<RatType> toStmt() {
		HavocStmt<RatType> result = stmt;
		if (result == null) {
			result = Havoc(clock);
			stmt = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockOpVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + clock.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FreeOp) {
			final FreeOp that = (FreeOp) obj;
			return this.getClock().equals(that.getClock());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Free(");
		sb.append(clock.getName());
		sb.append(")");
		return sb.toString();
	}

}
