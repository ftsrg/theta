package hu.bme.mit.theta.formalism.ta.op;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public final class FreeOp implements ClockOp {

	private static final int HASH_SEED = 2281;

	private final VarDecl<RatType> var;

	private volatile int hashCode = 0;
	private volatile HavocStmt<RatType> stmt = null;

	FreeOp(final VarDecl<RatType> var) {
		this.var = checkNotNull(var);
	}

	public VarDecl<RatType> getVar() {
		return var;
	}

	@Override
	public Collection<VarDecl<RatType>> getVars() {
		return ImmutableSet.of(var);
	}

	@Override
	public HavocStmt<RatType> toStmt() {
		HavocStmt<RatType> result = stmt;
		if (result == null) {
			result = Havoc(var);
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
			result = 31 * result + var.hashCode();
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
			return this.getVar().equals(that.getVar());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Free").add(var.getName()).toString();
	}

}
