package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.type.Type;

public interface IndexedConstDecl<DeclType extends Type> extends ConstDecl<DeclType> {

	VarDecl<DeclType> getVarDecl();

	int getIndex();

}
