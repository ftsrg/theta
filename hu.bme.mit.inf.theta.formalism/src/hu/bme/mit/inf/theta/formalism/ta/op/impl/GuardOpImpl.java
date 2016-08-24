package hu.bme.mit.inf.theta.formalism.ta.op.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.theta.formalism.common.stmt.impl.Stmts.Assume;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.theta.formalism.ta.op.GuardOp;
import hu.bme.mit.inf.theta.formalism.ta.utils.ClockOpVisitor;

final class GuardOpImpl implements GuardOp {

	private static final int HASH_SEED = 3533;

	private final ClockConstr constr;

	private volatile int hashCode = 0;
	private volatile AssumeStmt stmt = null;

	GuardOpImpl(final ClockConstr constr) {
		this.constr = checkNotNull(constr);
	}

	@Override
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
		final StringBuilder sb = new StringBuilder();
		sb.append("Guard(");
		sb.append(constr);
		sb.append(")");
		return sb.toString();
	}

}
