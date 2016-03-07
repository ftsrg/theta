package hu.bme.mit.inf.ttmc.formalism.stmt;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface DoStmt extends Stmt {
	
	public Stmt getDo();
	public Expr<? extends BoolType> getCond();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}
