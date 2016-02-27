package hu.bme.mit.inf.ttmc.program.stmt;

import hu.bme.mit.inf.ttmc.program.utils.StmtVisitor;

public interface Stmt {

	public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param);
	
}
