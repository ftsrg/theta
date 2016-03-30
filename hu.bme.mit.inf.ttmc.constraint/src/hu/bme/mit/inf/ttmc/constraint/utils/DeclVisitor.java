package hu.bme.mit.inf.ttmc.constraint.utils;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface DeclVisitor<P, R> {

	public <DeclType extends Type> R visit(ConstDecl<DeclType> decl, P param);

	public <DeclType extends Type> R visit(ParamDecl<DeclType> decl, P param);

}
