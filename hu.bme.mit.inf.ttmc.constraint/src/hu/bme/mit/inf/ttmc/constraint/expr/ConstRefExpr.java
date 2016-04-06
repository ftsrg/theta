package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface ConstRefExpr<DeclType extends Type> extends RefExpr<DeclType, ConstDecl<DeclType>> {
}
