package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.List;
import java.util.Optional;

public class XcfaLabelAction extends XcfaDeclAction{
	private final XcfaLabel label;
	private final Optional<Stmt> stmt;

	private XcfaLabelAction(final XcfaLabel label, final Optional<Stmt> stmt) {
		this.label = label;
		this.stmt = stmt;
	}

	public static XcfaLabelAction of(final XcfaLabel label, final Stmt stmt) {
		return new XcfaLabelAction(label, Optional.of(stmt));
	}

	public static XcfaLabelAction of(final XcfaLabel label) {
		return new XcfaLabelAction(label, Optional.empty());
	}

	@Override
	public List<Stmt> getStmts() {
		return stmt.map(List::of).orElse(List.of());
	}

	public XcfaLabel getLabel() {
		return label;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).add(label).toString();
	}
}
