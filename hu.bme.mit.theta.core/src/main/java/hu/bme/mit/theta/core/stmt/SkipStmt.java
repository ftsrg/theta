package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface SkipStmt extends Stmt {

	@Override
	default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
