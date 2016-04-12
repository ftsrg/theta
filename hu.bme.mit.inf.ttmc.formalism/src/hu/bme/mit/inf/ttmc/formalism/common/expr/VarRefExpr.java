package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.RefExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface VarRefExpr<DeclType extends Type> extends RefExpr<DeclType, VarDecl<DeclType>> {

}
