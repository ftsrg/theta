package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

/**
 * An adapter for XcfaStmtVisitor.
 * The XcfaStmtVisitor is too powerful for such an easy use case.
 * This is a much nicer interface (at least for me).
 */
public interface StmtExecutorInterface {
	<DeclType extends Type> void onAssign(AssignStmt<DeclType> stmt);
	<DeclType extends Type> void onHavoc(HavocStmt<DeclType> stmt);
	void onCall(CallStmt stmt);
	boolean onAssume(AssumeStmt stmt);
}
