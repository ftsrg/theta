package hu.bme.mit.inf.theta.formalism.common.stmt;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.utils.StmtVisitor;

public interface IfElseStmt extends Stmt {
	
	public Expr<? extends BoolType> getCond();
	public Stmt getThen();
	public Stmt getElse();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}