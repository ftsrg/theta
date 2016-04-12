package hu.bme.mit.inf.ttmc.core.utils;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface DeclVisitor<P, R> {

	public <DeclType extends Type> R visit(ConstDecl<DeclType> decl, P param);

	public <DeclType extends Type> R visit(ParamDecl<DeclType> decl, P param);

}
