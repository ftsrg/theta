package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.expr.RefExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;

public interface VarRefExpr<DeclType extends Type> extends RefExpr<DeclType, VarDecl<DeclType>> {

}
