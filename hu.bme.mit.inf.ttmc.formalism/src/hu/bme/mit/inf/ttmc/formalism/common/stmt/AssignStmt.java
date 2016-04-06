package hu.bme.mit.inf.ttmc.formalism.common.stmt;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface AssignStmt<DeclType extends Type, ExprType extends DeclType> extends Stmt {
	
	public VarDecl<DeclType> getVarDecl();
	public Expr<ExprType> getExpr();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
