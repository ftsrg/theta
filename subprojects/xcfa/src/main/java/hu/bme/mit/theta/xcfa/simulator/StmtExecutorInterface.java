package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

public interface StmtExecutorInterface {
	void assign(AssignStmt<?> stmt);
	void havoc(HavocStmt<?> stmt);
	void call(CallStmt stmt);
}
