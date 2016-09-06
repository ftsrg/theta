package hu.bme.mit.inf.theta.formalism.ta.op.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.theta.formalism.common.stmt.impl.Stmts.Assign;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.theta.formalism.ta.op.CopyOp;
import hu.bme.mit.inf.theta.formalism.ta.utils.ClockOpVisitor;

final class CopyOpImpl implements CopyOp {

	private static final int HASH_SEED = 1289;

	private final ClockDecl clock;
	private final ClockDecl value;

	private volatile int hashCode = 0;
	private volatile AssignStmt<RatType, RatType> stmt = null;

	CopyOpImpl(final ClockDecl clock, final ClockDecl value) {
		this.clock = checkNotNull(clock);
		this.value = checkNotNull(value);
	}

	@Override
	public ClockDecl getClock() {
		return clock;
	}

	@Override
	public ClockDecl getValue() {
		return value;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of(clock, value);
	}

	@Override
	public AssignStmt<RatType, RatType> toStmt() {
		AssignStmt<RatType, RatType> result = stmt;
		if (result == null) {
			result = Assign(clock, value.getRef());
			stmt = result;
		}
		return stmt;
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
			result = 31 * result + value.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof CopyOp) {
			final CopyOp that = (CopyOp) obj;
			return this.getClock().equals(that.getClock()) && this.getValue().equals(that.getValue());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Copy(");
		sb.append(clock.getName());
		sb.append(", ");
		sb.append(value.getName());
		return sb.toString();
	}

}
