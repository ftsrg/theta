package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;

public interface DeclVisitor<P, R> {

	<DeclType extends Type> R visit(ConstDecl<DeclType> decl, P param);

	<DeclType extends Type> R visit(ParamDecl<DeclType> decl, P param);

}
