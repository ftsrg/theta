package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface IfStmt extends Stmt {

	Expr<? extends BoolType> getCond();

	Stmt getThen();

	@Override
	default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
