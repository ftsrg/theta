package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Type;

public interface XcfaLabelVisitor<P, R> extends StmtVisitor<P, R> {
	R visit(XcfaLabel.AtomicBeginXcfaLabel label, P param);
	R visit(XcfaLabel.AtomicEndXcfaLabel label, P param);
	R visit(XcfaLabel.ProcedureCallXcfaLabel label, P param);
	R visit(XcfaLabel.StartThreadXcfaLabel label, P param);
	R visit(XcfaLabel.JoinThreadXcfaLabel label, P param);
	<T extends Type> R visit(XcfaLabel.LoadXcfaLabel<T> label, P param);
	<T extends Type> R visit(XcfaLabel.StoreXcfaLabel<T> label, P param);
	R visit(XcfaLabel.FenceXcfaLabel label, P param);
	R visit(XcfaLabel.StmtXcfaLabel label, P param);
	R visit(XcfaLabel.SequenceLabel sequenceLabel, P param);
	R visit(XcfaLabel.NondetLabel nondetLabel, P param);

}
