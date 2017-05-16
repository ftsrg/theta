package hu.bme.mit.theta.formalism.ta.op;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.Exprs.Int;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public final class ResetOp implements ClockOp {

	private static final int HASH_SEED = 4507;

	private final ClockDecl clock;
	private final int value;

	private volatile int hashCode = 0;
	private volatile AssignStmt<RatType, IntType> stmt = null;

	ResetOp(final ClockDecl clock, final int value) {
		checkArgument(value >= 0);
		this.clock = checkNotNull(clock);
		this.value = value;
	}

	public ClockDecl getClock() {
		return clock;
	}

	public int getValue() {
		return value;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of(clock);
	}

	@Override
	public AssignStmt<RatType, IntType> toStmt() {
		AssignStmt<RatType, IntType> result = stmt;
		if (result == null) {
			result = Assign(clock, Int(value));
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
			result = 31 * result + value;
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ResetOp) {
			final ResetOp that = (ResetOp) obj;
			return this.getClock().equals(that.getClock()) && this.getValue() == that.getValue();
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Reset").add(clock.getName()).add(value).toString();
	}

}
