package hu.bme.mit.inf.theta.program.ui.transform;

import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.theta.program.model.Statement;

public interface StmtTransformator {

	public Stmt transform(Statement statement);

}
