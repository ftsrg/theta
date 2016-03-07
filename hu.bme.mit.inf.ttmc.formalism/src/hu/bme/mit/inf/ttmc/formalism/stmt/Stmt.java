package hu.bme.mit.inf.ttmc.formalism.stmt;

import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface Stmt {

	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param);
	
}
