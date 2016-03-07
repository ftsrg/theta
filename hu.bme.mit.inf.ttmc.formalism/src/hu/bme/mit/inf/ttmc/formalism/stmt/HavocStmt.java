package hu.bme.mit.inf.ttmc.formalism.stmt;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.StmtVisitor;

public interface HavocStmt<DeclType extends Type> extends Stmt {
	
	public VarDecl<DeclType> getVarDecl();
	
	@Override
	public default <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
}
