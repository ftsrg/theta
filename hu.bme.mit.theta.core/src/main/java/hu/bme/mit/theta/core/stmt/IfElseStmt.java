package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface IfElseStmt extends Stmt {

	public Expr<? extends BoolType> getCond();

	public Stmt getThen();

	public Stmt getElse();

	@Override
	public default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}