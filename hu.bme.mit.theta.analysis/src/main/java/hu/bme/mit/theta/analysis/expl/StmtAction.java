package hu.bme.mit.theta.analysis.expl;

import java.util.List;

import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.stmt.Stmt;

public interface StmtAction extends ExprAction {
	List<Stmt> getStmts();
}
