package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.type.Type;

public interface VarDecl<DeclType extends Type> extends Decl<DeclType> {

	IndexedConstDecl<DeclType> getConstDecl(int index);

}
