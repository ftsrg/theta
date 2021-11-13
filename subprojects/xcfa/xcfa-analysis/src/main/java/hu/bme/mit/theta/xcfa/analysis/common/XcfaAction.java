package hu.bme.mit.theta.xcfa.analysis.common;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.List;
import java.util.stream.Collectors;

public abstract class XcfaAction extends StmtAction {
	public static XcfaAction create(final XcfaEdge edge) {
		return new SimpleXcfaAction(edge);
	}

	public abstract XcfaLocation getSource();
	public abstract XcfaLocation getTarget();
	public abstract List<XcfaLabel> getLabels();

	@Override
	public String toString() {
		return Utils.lispStringBuilder("XcfaAction").add(getSource().getName() + "->" + getTarget().getName()).add(getLabels()).toString();
	}

	private static class SimpleXcfaAction extends XcfaAction {
		private final XcfaEdge edge;

		private SimpleXcfaAction(XcfaEdge edge) {
			this.edge = edge;
		}

		@Override
		public List<Stmt> getStmts() {
			return edge.getLabels().stream().map(XcfaLabel::getStmt).collect(Collectors.toList());
		}

		@Override
		public XcfaLocation getSource() {
			return edge.getSource();
		}

		@Override
		public XcfaLocation getTarget() {
			return edge.getTarget();
		}

		@Override
		public List<XcfaLabel> getLabels() {
			return edge.getLabels();
		}
	}
}
