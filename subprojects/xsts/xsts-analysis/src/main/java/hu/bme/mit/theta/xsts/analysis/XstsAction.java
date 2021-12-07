package hu.bme.mit.theta.xsts.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public final class XstsAction extends StmtAction {

	private final List<Stmt> stmts;

	private XstsAction(final List<Stmt> stmts) {
		this.stmts = stmts;
	}

	public static XstsAction create(final Stmt stmt) {
		return new XstsAction(ImmutableList.of(stmt));
	}

	public static XstsAction create(final List<Stmt> stmts) {
		return new XstsAction(stmts);
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XstsAction) {
			final XstsAction that = (XstsAction) obj;
			return this.stmts.equals(that.stmts);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(stmts).toString();
	}
}
