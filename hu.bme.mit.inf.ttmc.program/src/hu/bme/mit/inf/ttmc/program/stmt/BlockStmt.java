package hu.bme.mit.inf.ttmc.program.stmt;

import java.util.List;

import hu.bme.mit.inf.ttmc.program.utils.StmtVisitor;

public interface BlockStmt extends Stmt {
	
	public List<? extends Stmt> getStmts();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}
