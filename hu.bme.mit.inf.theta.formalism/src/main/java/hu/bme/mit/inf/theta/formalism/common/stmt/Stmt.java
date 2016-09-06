package hu.bme.mit.inf.theta.formalism.common.stmt;

import hu.bme.mit.inf.theta.formalism.utils.StmtVisitor;

public interface Stmt {

	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param);
	
}
