package hu.bme.mit.inf.ttmc.formalism.stmt;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface ReturnStmt<ReturnType extends Type> extends Stmt {
	
	Expr<? extends ReturnType> getExpr();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
