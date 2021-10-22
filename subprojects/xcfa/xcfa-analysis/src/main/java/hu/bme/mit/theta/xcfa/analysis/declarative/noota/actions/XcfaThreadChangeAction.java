package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public class XcfaThreadChangeAction extends XcfaDeclAction{
	private final Integer process;

	private XcfaThreadChangeAction(final Integer process) {
		this.process = process;
	}

	public static XcfaThreadChangeAction of(final Integer process) {
		return new XcfaThreadChangeAction(process);
	}

	@Override
	public List<Stmt> getStmts() {
		return List.of();
	}

	public Integer getProcess() {
		return process;
	}


	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).add(process).toString();
	}

}
