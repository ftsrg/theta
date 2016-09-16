package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public interface HavocStmt<DeclType extends Type> extends Stmt {

	public VarDecl<DeclType> getVarDecl();

	@Override
	public default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
