package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface ParamRefExpr<DeclType extends Type> extends RefExpr<DeclType, ParamDecl<DeclType>> {
}
