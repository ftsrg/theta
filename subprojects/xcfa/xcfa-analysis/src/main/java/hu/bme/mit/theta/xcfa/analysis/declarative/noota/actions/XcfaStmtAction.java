package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public class XcfaStmtAction extends XcfaDeclAction {
	private final List<Stmt> stmts;

	private XcfaStmtAction(final List<Stmt> stmts) {
		this.stmts = List.copyOf(stmts);
	}

	public static XcfaStmtAction of(final List<Stmt> stmts) {
		return new XcfaStmtAction(stmts);
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}



	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).add(stmts).toString();
	}
}
