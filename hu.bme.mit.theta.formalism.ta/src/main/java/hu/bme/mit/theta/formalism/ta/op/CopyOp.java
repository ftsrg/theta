package hu.bme.mit.theta.formalism.ta.op;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.RatType;

public final class CopyOp implements ClockOp {

	private static final int HASH_SEED = 1289;

	private final VarDecl<RatType> var;
	private final VarDecl<RatType> value;

	private volatile int hashCode = 0;
	private volatile AssignStmt<RatType, RatType> stmt = null;

	CopyOp(final VarDecl<RatType> var, final VarDecl<RatType> value) {
		this.var = checkNotNull(var);
		this.value = checkNotNull(value);
	}

	public VarDecl<RatType> getVar() {
		return var;
	}

	public VarDecl<RatType> getValue() {
		return value;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(var, value);
	}

	@Override
	public AssignStmt<RatType, RatType> toStmt() {
		AssignStmt<RatType, RatType> result = stmt;
		if (result == null) {
			result = Assign(var, value.getRef());
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
			result = 31 * result + var.hashCode();
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
			return this.getVar().equals(that.getVar()) && this.getValue().equals(that.getValue());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Copy(");
		sb.append(var.getName());
		sb.append(", ");
		sb.append(value.getName());
		return sb.toString();
	}

}
