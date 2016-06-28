package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface ConstRefExpr<DeclType extends Type> extends RefExpr<DeclType, ConstDecl<DeclType>> {
}
