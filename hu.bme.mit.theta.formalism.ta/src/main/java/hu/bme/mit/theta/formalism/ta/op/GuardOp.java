package hu.bme.mit.theta.formalism.ta.op;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

import java.util.Collection;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public final class GuardOp implements ClockOp {

	private static final int HASH_SEED = 3533;

	private final ClockConstr constr;

	private volatile int hashCode = 0;
	private volatile AssumeStmt stmt = null;

	GuardOp(final ClockConstr constr) {
		this.constr = checkNotNull(constr);
	}

	public ClockConstr getConstr() {
		return constr;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return constr.getClocks();
	}

	@Override
	public AssumeStmt toStmt() {
		AssumeStmt result = stmt;
		if (result == null) {
			result = Assume(constr.toExpr());
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
			result = 31 * result + constr.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof GuardOp) {
			final GuardOp that = (GuardOp) obj;
			return this.getConstr().equals(that.getConstr());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Guard").add(constr).toString();
	}

}
