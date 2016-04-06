package hu.bme.mit.inf.ttmc.formalism.common.stmt;

import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface SkipStmt extends Stmt {

	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}
