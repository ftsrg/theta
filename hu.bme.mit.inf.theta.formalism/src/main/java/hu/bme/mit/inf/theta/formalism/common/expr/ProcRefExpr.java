package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.expr.RefExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.type.ProcType;

public interface ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>, ProcDecl<ReturnType>> {

}
