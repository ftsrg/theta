package hu.bme.mit.inf.ttmc.formalism.common.stmt;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface DeclStmt<DeclType extends Type> extends Stmt {

	public VarDecl<DeclType> getVarDecl();

	@Override
	public default <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

}
