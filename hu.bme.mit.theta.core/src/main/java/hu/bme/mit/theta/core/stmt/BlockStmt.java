package hu.bme.mit.theta.core.stmt;

import java.util.List;

import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface BlockStmt extends Stmt {

	List<? extends Stmt> getStmts();

	@Override
	default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
