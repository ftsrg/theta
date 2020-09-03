package hu.bme.mit.theta.xsts.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public final class XstsAction extends StmtAction {

	private final Stmt stmt;

	private XstsAction(final Stmt stmt) {
		this.stmt = stmt;
	}

	public static XstsAction create(final Stmt stmt) {
		return new XstsAction(stmt);
	}

	@Override
	public List<Stmt> getStmts() {
		return ImmutableList.of(stmt);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XstsAction) {
			final XstsAction that = (XstsAction) obj;
			return this.stmt.equals(that.stmt);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().add(stmt).toString();
	}
}
