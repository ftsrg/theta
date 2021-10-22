package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;

public class XcfaAdvanceAction extends XcfaDeclAction{
	private final XcfaLocation target;

	private XcfaAdvanceAction(final XcfaLocation target) {
		this.target = target;
	}

	public static XcfaAdvanceAction of(final XcfaLocation target) {
		return new XcfaAdvanceAction(target);
	}

	@Override
	public List<Stmt> getStmts() {
		return List.of();
	}

	public XcfaLocation getTarget() {
		return target;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).add(target).toString();
	}
}
