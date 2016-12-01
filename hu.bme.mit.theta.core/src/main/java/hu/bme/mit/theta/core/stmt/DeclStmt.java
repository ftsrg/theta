package hu.bme.mit.theta.core.stmt;

import java.util.Optional;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface DeclStmt<DeclType extends Type, ExprType extends DeclType> extends Stmt {

	VarDecl<DeclType> getVarDecl();

	Optional<Expr<ExprType>> getInitVal();

	@Override
	default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
