package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface ParamRefExpr<DeclType extends Type> extends RefExpr<DeclType, ParamDecl<DeclType>> {
}
