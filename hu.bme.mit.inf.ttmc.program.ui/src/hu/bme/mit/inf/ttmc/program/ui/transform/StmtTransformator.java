package hu.bme.mit.inf.ttmc.program.ui.transform;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.program.model.Statement;

public interface StmtTransformator {

	public Stmt transform(Statement statement);

}
