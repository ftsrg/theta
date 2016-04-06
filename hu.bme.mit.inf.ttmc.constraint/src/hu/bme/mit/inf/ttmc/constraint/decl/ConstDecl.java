package hu.bme.mit.inf.ttmc.constraint.decl;

import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface ConstDecl<DeclType extends Type> extends Decl<DeclType, ConstDecl<DeclType>> {

	@Override
	public ConstRefExpr<DeclType> getRef();

}
