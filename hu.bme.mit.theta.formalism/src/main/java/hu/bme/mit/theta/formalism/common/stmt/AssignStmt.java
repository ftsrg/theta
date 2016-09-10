package hu.bme.mit.theta.formalism.common.stmt;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.utils.StmtVisitor;

public interface AssignStmt<DeclType extends Type, ExprType extends DeclType> extends Stmt {
	
	public VarDecl<DeclType> getVarDecl();
	public Expr<ExprType> getExpr();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
