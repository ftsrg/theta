package hu.bme.mit.inf.ttmc.formalism.common.stmt;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface WhileStmt extends Stmt {
	
	public Expr<? extends BoolType> getCond();
	public Stmt getDo();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}
