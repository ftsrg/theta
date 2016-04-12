package hu.bme.mit.inf.ttmc.formalism.common.stmt;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface DeclStmt<DeclType extends Type, ExprType extends DeclType> extends Stmt {

	public VarDecl<DeclType> getVarDecl();

	public Optional<Expr<ExprType>> getInitVal();

	@Override
	public default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
