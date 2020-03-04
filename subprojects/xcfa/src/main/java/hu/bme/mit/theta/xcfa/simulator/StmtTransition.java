package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.simulator.partialorder.StmtDeclCollector;
import hu.bme.mit.theta.xcfa.simulator.partialorder.StmtNotReadOnlyDeclCollector;

import java.util.Collection;
import java.util.HashSet;

/**
 * A transition with an associated edge.
 * Almost every transition is alike, except LeaveTransition, at the moment.
 * Uses StmtExecutorInterface through EnabledStmtVisitor and StateUpdateVisitor to process statements.
 * An exception is LeaveTransition, which leaves a call.
 *
 * A transition instance should be independent of ExplStates.
 *
 * Note: In the future, to be able to cache these transitions, one should not store state of the explicit state in use.
 *
 * Note: Multiple statements on the same edge is not supported.
 *   Enabledness cannot be determined without running previous stmts
 *   Function calls will mess everything up
 *
 * Abstract so I can "mock" it in the tests (without actually using ugly reflection)
 */
public abstract class StmtTransition extends ProcessTransition {

	public StmtTransition(XCFA.Process p) {
		super(p);
	}

	@Override
	public abstract void execute(ExplState state);

	@Override
	public abstract boolean enabled(ExplState state);

	// read vars that don't change
	public abstract Collection<Decl<?>> getRWVars();

	// read vars that do change
	public abstract Collection<Decl<?>> getWVars();
}
